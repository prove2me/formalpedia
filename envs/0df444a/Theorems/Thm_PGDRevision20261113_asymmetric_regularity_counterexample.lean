-- Prove2me | Theorems.Thm_PGDRevision20261113_asymmetric_regularity_counterexample
-- name    : PGDRevision20261113.asymmetric_regularity_counterexample
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:07:47.402208+00:00
-- url     : https://prove2.me/theorems/752d6596-495f-4105-87ce-9be3a15b25eb
-- title:
--   Continuity without asymmetric differentiability permits a continuum of optima
-- statement:
--   On the real line set $b(x)=1+x^2$, $\lambda=1$, and $k_c(x)=b(x)^c$ for $c\ge0$. Define the loss curvature by
--   $$
--   A(x)=\begin{cases}0,&x\le-1,\\
--   (29+11x+11x^2+29x^3)/180,&-1<x\le1,\\4/9,&x>1.\end{cases}
--   $$
--   This function is continuous, lies in $[0,4/9]$, and is not differentiable at either $-1$ or $1$. Its twice-integrated, zero-normalized primitive is convex, is $C^2$, has second derivative $A$, and has a $4/9$-Lipschitz derivative.
--
--   With $E=(pb^c-A)/(pb^c+b)$, the entire set of minimizing pairs is
--   $$
--   \left\{\left(c,\frac29\,2^{-c}\right):0\le c\le1\right\},\qquad \rho_*=1/10.
--   $$
--   Every displayed pair satisfies the global envelope on the whole real line. This gives distinct optimal exponents and explains the differentiability requirement in the asymmetric classification.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [Finite-feature design](https://prove2.me/theorems/4dd784f1-031f-48f0-b0d2-951480e5aee4) · [regularity band identities](https://prove2.me/theorems/62f3e8cd-fdf6-4e32-8196-1e13a218705e)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 5, paragraph Why asymmetric regularity matters; sections/05_geometry_classification.tex, eq:regularity_counterexample.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.asymmetric_regularity_counterexample : RegularityCounterexampleClaim := by sorry
