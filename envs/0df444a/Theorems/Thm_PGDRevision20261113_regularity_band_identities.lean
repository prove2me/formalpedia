-- Prove2me | Theorems.Thm_PGDRevision20261113_regularity_band_identities
-- name    : PGDRevision20261113.regularity_band_identities
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:08:21.736503+00:00
-- url     : https://prove2.me/theorems/62f3e8cd-fdf6-4e32-8196-1e13a218705e
-- title:
--   Exact band identities for the asymmetric regularity counterexample
-- statement:
--   For $-1\le x\le1$, let $A$ be the piecewise curvature of the regularity counterexample, and put $L=(1-x^2)/10$, $U=2(1+x^2)/9$. Then
--   $$
--   A-L=\frac{(x+1)(11+29x^2)}{180},\qquad
--   U-A=\frac{(1-x)(11+29x^2)}{180},\qquad L\le A\le U.
--   $$
--   The identities include both endpoints and supply the common bands used for the continuum of minimizing geometry parameters.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [asymmetric regularity counterexample](https://prove2.me/theorems/752d6596-495f-4105-87ce-9be3a15b25eb)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 5, regularity counterexample; sections/05_geometry_classification.tex, eq:regularity_counterexample and following identities.

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
open PGDRevision20261113

theorem PGDRevision20261113.regularity_band_identities : RegularityBandIdentitiesClaim := by sorry
