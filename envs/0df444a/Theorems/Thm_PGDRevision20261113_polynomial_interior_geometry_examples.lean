-- Prove2me | Theorems.Thm_PGDRevision20261113_polynomial_interior_geometry_examples
-- name    : PGDRevision20261113.polynomial_interior_geometry_examples
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:07:58.193592+00:00
-- url     : https://prove2.me/theorems/dc636fa7-9f09-4d18-b4eb-061ec9356983
-- title:
--   Both polynomial penalties select a strictly interior geometry
-- statement:
--   The two penalty-curvature profiles on $\mathbb R$ are
--   $$
--   b_1(x)=1+x^2,\qquad b_2(x)=1+x^2+x^3+x^4.
--   $$
--   For either choice, use $A(x)=a(b(x))$, penalty curvature $\lambda b(x)$, and generator curvature $b(x)^c$, with $c\ge0$ and inverse stepsize $p>0$. The error is $(pb^c-A)/(pb^c+\lambda b)$ and its norm is the supremum on the entire real line.
--
--   For $a(s)=2-1/s$ and $\lambda=1$, both models satisfy the classification hypotheses and each has a unique optimal pair with
--   $$0<c_*<1.$$
--   For $b_1$, the prescribed loss is explicitly
--   $$
--   \psi(x)=x^2-x\arctan x+\tfrac12\log(1+x^2),\qquad
--   1\le\psi''(x)=2-\frac1{1+x^2}<2.
--   $$
--   The claim concerns the loss specified as $a\circ b$ for each penalty.
--
--   **Related results.** [Curvature-relation reduction](https://prove2.me/theorems/569bd574-8d1b-4c8d-8e71-3c2b232c84f0) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 6.2, last paragraph; sections/06_classification_applications.tex, sec:real_examples.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.polynomial_interior_geometry_examples : PolynomialInteriorExamplesClaim := by sorry
