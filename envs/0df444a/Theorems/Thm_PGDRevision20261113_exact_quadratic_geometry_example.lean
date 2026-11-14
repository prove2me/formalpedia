-- Prove2me | Theorems.Thm_PGDRevision20261113_exact_quadratic_geometry_example
-- name    : PGDRevision20261113.exact_quadratic_geometry_example
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:07:53.298175+00:00
-- url     : https://prove2.me/theorems/8f4fd18c-871b-4639-b371-b1b486f45e83
-- title:
--   An exact quadratic optimum for a nonconstant loss
-- statement:
--   On $I=(-1,1)$, let the loss curvature be $A(t)$, the penalty curvature be $B(t)=\lambda/(1-t^2)$, and the candidate curvature be
--   $$
--   k_c(t)=\tfrac12[(1+t)^{-c}+(1-t)^{-c}],\qquad c\ge0.
--   $$
--   For $p>0$, write
--   $$
--   E_{c,p}(t)=\frac{pk_c(t)-A(t)}{pk_c(t)+B(t)},\qquad \rho(c,p)=\sup_{t\in I}|E_{c,p}(t)|.
--   $$
--   The objective is allowed a free linear tilt, with exact implicit updates and a fixed geometry and inverse stepsize. The finite-horizon criterion $\Omega_N$ is the supremum of the squared objective-gradient ratio over those tilts and nonstationary initial states.
--
--   For $A(t)=12-9t^2$ and $\lambda=10$, the unique minimizing pair and exact rate are
--   $$
--   (c_*,p_*)=(0,10),\qquad \rho_*=1/10.
--   $$
--   At this pair the global envelope $|E(t)|\le\rho_*$ holds throughout $I$. The errors at $t=0$ and $t=\sqrt{2/3}$ are respectively $-1/10$ and $1/10$.
--
--   For every finite $N\ge1$, the optimal value is $\Omega_N=\rho_*^{2N}$, and the same pair uniquely minimizes this criterion. The admissibility conditions, global envelope, exact contacts, uniqueness, and finite-horizon assertions are all included in the formal statement.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [quadratic envelope identities](https://prove2.me/theorems/ef3d5237-245b-4827-a5a7-77fe3f7e81c3)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 8, exact classification examples table and accompanying certificates; sections/08_exact_classification_examples.tex, sec:exact_examples; tab:selection_exact.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.exact_quadratic_geometry_example : ExactQuadraticExampleClaim := by sorry
