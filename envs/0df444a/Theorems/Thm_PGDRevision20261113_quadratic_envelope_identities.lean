-- Prove2me | Theorems.Thm_PGDRevision20261113_quadratic_envelope_identities
-- name    : PGDRevision20261113.quadratic_envelope_identities
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:08:15.199892+00:00
-- url     : https://prove2.me/theorems/ef3d5237-245b-4827-a5a7-77fe3f7e81c3
-- title:
--   Two rational identities certify the quadratic example's global envelope
-- statement:
--   For $0\le u\le1$ set $e(u)=(9u-2)(1-u)/[10(2-u)]$. Then
--   $$
--   e(u)+\frac1{10}=\frac{u(10-9u)}{10(2-u)},\qquad
--   \frac1{10}-e(u)=\frac{(3u-2)^2}{10(2-u)},\qquad |e(u)|\le\frac1{10}.
--   $$
--   These exact rational identities supply the full-interval envelope for the quadratic classification example and its real-line curvature-relation counterparts.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [exact quadratic geometry example](https://prove2.me/theorems/8f4fd18c-871b-4639-b371-b1b486f45e83)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 8, first exact envelope; sections/08_exact_classification_examples.tex, eq:exact_quadratic_envelope.

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
open PGDRevision20261113

theorem PGDRevision20261113.quadratic_envelope_identities : QuadraticEnvelopeIdentitiesClaim := by sorry
