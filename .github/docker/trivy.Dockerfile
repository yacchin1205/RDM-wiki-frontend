# The application Dockerfile expects an RDM-osf.io checkout as its build context.
# This standalone scan image captures this repository's base OS and locked JS packages.
FROM node:21-alpine

WORKDIR /code

COPY package.json yarn.lock ./
