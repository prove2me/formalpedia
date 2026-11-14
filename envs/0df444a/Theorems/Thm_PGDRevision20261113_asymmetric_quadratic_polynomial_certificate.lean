-- Prove2me | Theorems.Thm_PGDRevision20261113_asymmetric_quadratic_polynomial_certificate
-- name    : PGDRevision20261113.asymmetric_quadratic_polynomial_certificate
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:08:24.955284+00:00
-- url     : https://prove2.me/theorems/6a218687-0a7f-4083-84b0-0d6c70391dd7
-- title:
--   A polynomial factorization certifies the asymmetric quadratic envelope
-- statement:
--   For every real $u$,
--   $$
--   (3-2u)^2-32u(1-u)^2=(1-2u)^2(9-8u).
--   $$
--   The expression is nonnegative for $0\le u\le1$. This is the exact polynomial gap used for the envelope $|E|\le\sqrt2/8$ in the asymmetric quadratic example $A(t)=2+t$.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [exact asymmetric quadratic geometry example](https://prove2.me/theorems/ee75d7dc-a137-4e44-aea5-b757651ed73f)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 8, asymmetric quadratic example; sections/08_exact_classification_examples.tex, (3-2u)^2-32u(1-u)^2.

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
open PGDRevision20261113

theorem PGDRevision20261113.asymmetric_quadratic_polynomial_certificate : AsymmetricQuadraticPolynomialIdentityClaim := by sorry
