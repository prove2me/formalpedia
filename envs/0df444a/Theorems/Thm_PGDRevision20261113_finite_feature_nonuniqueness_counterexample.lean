-- Prove2me | Theorems.Thm_PGDRevision20261113_finite_feature_nonuniqueness_counterexample
-- name    : PGDRevision20261113.finite_feature_nonuniqueness_counterexample
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:08:10.415202+00:00
-- url     : https://prove2.me/theorems/48884d70-daa8-4d9b-a622-d0e2e9b388f9
-- title:
--   One smooth bump feature gives distinct optimal geometries
-- statement:
--   On $\mathbb R$ let
--   $$
--   A(x)=3+\frac9{1+x^2},\quad B(x)=10(1+x^2),\quad
--   h(x)=(x-3)_+^2(4-x)_+^2,\quad k_\theta(x)=e^{\theta h(x)}.
--   $$
--   The corresponding loss and penalty can be taken as
--   $$
--   f(x)=\tfrac32x^2+9x\arctan x-\tfrac92\log(1+x^2),\qquad
--   g(x)=10(x^2/2+x^4/12).
--   $$
--   The feature is $C^1$, vanishes outside $[3,4]$, and has $h(7/2)=1/16$. These data satisfy the finite-feature design hypotheses.
--
--   Over every $\theta\in\mathbb R$ and $p>0$, the error norm is at least $1/10$. Every $\theta\le0$ attains that bound at $p=10$:
--   $$
--   \rho(\theta,10)=1/10,\qquad \Omega_N(\theta,10)=(1/10)^{2N}\quad(N\ge1).
--   $$
--   Different feature parameters give different curvature values at $7/2$, so this is nonuniqueness of geometries. The statement asserts optimality for all nonpositive parameters, without claiming that these exhaust every possible optimal positive parameter.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [Finite-feature design](https://prove2.me/theorems/4dd784f1-031f-48f0-b0d2-951480e5aee4) · [polynomial quadratic geometry examples](https://prove2.me/theorems/56fed2bb-bdce-4491-8f05-d5959791e9df)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 4.1, paragraph Uniqueness can fail outside ordered families; sections/04_bregman_framework.tex, Uniqueness can fail outside ordered families.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.finite_feature_nonuniqueness_counterexample : FiniteFeatureNonuniquenessClaim := by sorry
