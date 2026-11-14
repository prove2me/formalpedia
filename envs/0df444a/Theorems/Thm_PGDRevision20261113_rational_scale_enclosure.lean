-- Prove2me | Theorems.Thm_PGDRevision20261113_rational_scale_enclosure
-- name    : PGDRevision20261113.rational_scale_enclosure
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:08:17.421346+00:00
-- url     : https://prove2.me/theorems/c8566766-97a3-4d51-8b5d-87b15cd4706b
-- title:
--   A logarithmic scale bound gives rational multiplicative endpoints
-- statement:
--   For positive $p,\widehat p$ and $0\le b<1$, a logarithmic scale bound implies
--   $$
--   |\log(p/\widehat p)|\le b
--   \quad\Longrightarrow\quad
--   \widehat p(1-b)\le p\le\frac{\widehat p}{1-b}.
--   $$
--   When $b$ and $\widehat p$ are rational, both endpoints are rational. This implication is the scale conversion used in the approximate-contact parameter certificates.
--
--   **Related results.** [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef) · [Error-band equivalence](https://prove2.me/theorems/672f9ba5-f16d-4b26-bfdf-ed78d3d74fd5)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 7, rational scale enclosure; sections/07_quantitative_certificates.tex, eq:bg_rational_scale.

import Definitions.Def_PGDRevision20261113_NumericalCertificates
open PGDRevision20261113

theorem PGDRevision20261113.rational_scale_enclosure : RationalScaleEnclosureClaim := by sorry
