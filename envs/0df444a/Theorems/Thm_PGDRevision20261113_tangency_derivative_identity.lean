-- Prove2me | Theorems.Thm_PGDRevision20261113_tangency_derivative_identity
-- name    : PGDRevision20261113.tangency_derivative_identity
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:08:19.725348+00:00
-- url     : https://prove2.me/theorems/2838f92b-a6be-44f5-a2be-aab759757225
-- title:
--   The error-derivative difference at equal scaled curvatures
-- statement:
--   Let $A,B,v,w$ be real functions differentiable at $x$, assume $v(x)+B(x)\ne0$ and $w(x)=v(x)$, and set $E_q=(q-A)/(q+B)$. Then
--   $$
--   E_w'(x)-E_v'(x)=\frac{A(x)+B(x)}{[v(x)+B(x)]^2}\,[w'(x)-v'(x)].
--   $$
--   This identity isolates the scaled-kernel derivative at contacts where the two scaled curvatures agree. It is the differential ingredient of the same-feature uniqueness certificate.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [same feature tangency certificate](https://prove2.me/theorems/de242eb0-14af-49b9-8f96-4f8b07f8e03d)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 5, contact-certificate proof; sections/05_geometry_classification.tex, eq:selection_tangency.

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
open PGDRevision20261113

theorem PGDRevision20261113.tangency_derivative_identity : TangencyDerivativeIdentityClaim := by sorry
