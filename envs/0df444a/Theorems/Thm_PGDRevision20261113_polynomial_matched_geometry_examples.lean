-- Prove2me | Theorems.Thm_PGDRevision20261113_polynomial_matched_geometry_examples
-- name    : PGDRevision20261113.polynomial_matched_geometry_examples
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:07:57.607049+00:00
-- url     : https://prove2.me/theorems/eb4d825a-2db0-4a60-95f4-1bbe39101c23
-- title:
--   Both polynomial penalties have the same exact matched optimum
-- statement:
--   The two penalty-curvature profiles on $\mathbb R$ are
--   $$
--   b_1(x)=1+x^2,\qquad b_2(x)=1+x^2+x^3+x^4.
--   $$
--   For either choice, use $A(x)=a(b(x))$, penalty curvature $\lambda b(x)$, and generator curvature $b(x)^c$, with $c\ge0$ and inverse stepsize $p>0$. The error is $(pb^c-A)/(pb^c+\lambda b)$ and its norm is the supremum on the entire real line.
--
--   For $a(s)=1-1/s$ and $\lambda=1$, both choices of the spatial penalty have
--   $$
--   (c_*,p_*,\rho_*)=(1,1/8,1/9).
--   $$
--   The stated pair is globally and uniquely optimal, has a global error envelope, and uniquely minimizes every finite-horizon relative-gradient criterion, whose value is $(1/9)^{2N}$ for $N\ge1$.
--
--   **Related results.** [Curvature-relation reduction](https://prove2.me/theorems/569bd574-8d1b-4c8d-8e71-3c2b232c84f0) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 6.2, examples following Corollary 6.3; sections/06_classification_applications.tex, cor:curvature_relation; sec:real_examples.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.polynomial_matched_geometry_examples : PolynomialMatchedExamplesClaim := by sorry
