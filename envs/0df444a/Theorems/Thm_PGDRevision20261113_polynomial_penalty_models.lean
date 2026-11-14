-- Prove2me | Theorems.Thm_PGDRevision20261113_polynomial_penalty_models
-- name    : PGDRevision20261113.polynomial_penalty_models
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:07:54.633046+00:00
-- url     : https://prove2.me/theorems/7745bf8d-dbbf-4bb6-81d3-be854efa3535
-- title:
--   Two strongly convex polynomial penalties satisfy the real-line model
-- statement:
--   The two penalty-curvature profiles on $\mathbb R$ are
--   $$
--   b_1(x)=1+x^2,\qquad b_2(x)=1+x^2+x^3+x^4.
--   $$
--   For either choice, use $A(x)=a(b(x))$, penalty curvature $\lambda b(x)$, and generator curvature $b(x)^c$, with $c\ge0$ and inverse stepsize $p>0$. The error is $(pb^c-A)/(pb^c+\lambda b)$ and its norm is the supremum on the entire real line.
--
--   For every $\lambda>0$, the ordinary polynomials
--   $$
--   r_1(x)=\lambda(x^2/2+x^4/12),\quad
--   r_2(x)=\lambda(x^2/2+x^4/12+x^5/20+x^6/30)
--   $$
--   have second derivatives $\lambda b_1$ and $\lambda b_2$. Both curvature profiles are at least one, and $b_2'(x)=x(2+3x+4x^2)$. In particular, with constant loss curvature one, both data sets satisfy all real-line classification hypotheses, including differentiability, the strict derivative signs, and growth at infinity.
--
--   **Related results.** [Curvature-relation reduction](https://prove2.me/theorems/569bd574-8d1b-4c8d-8e71-3c2b232c84f0) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 6.2, Real-line penalties and curvature relations; sections/06_classification_applications.tex, sec:real_examples.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.polynomial_penalty_models : PolynomialPenaltyModelsClaim := by sorry
