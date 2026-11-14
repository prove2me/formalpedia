-- Prove2me | Theorems.Thm_PGDRevision20261113_exact_matched_geometry_example
-- name    : PGDRevision20261113.exact_matched_geometry_example
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:07:47.181347+00:00
-- url     : https://prove2.me/theorems/e559ae8a-f3b6-4e1f-bc49-a1399603da3e
-- title:
--   An exact penalty-matched optimum with a vanishing center curvature
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
--   For $A(t)=t^2$ and $\lambda=1$, the unique minimizing pair and exact rate are
--   $$
--   (c_*,p_*)=(1,1/8),\qquad \rho_*=1/9.
--   $$
--   At this pair the global envelope $|E(t)|\le\rho_*$ holds throughout $I$. The errors at $t=0$ and $t=1/\sqrt2$ are respectively $1/9$ and $-1/9$.
--
--   For every finite $N\ge1$, the optimal value is $\Omega_N=\rho_*^{2N}$, and the same pair uniquely minimizes this criterion. The admissibility conditions, global envelope, exact contacts, uniqueness, and finite-horizon assertions are all included in the formal statement.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [polynomial matched geometry examples](https://prove2.me/theorems/eb4d825a-2db0-4a60-95f4-1bbe39101c23)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 8, exact classification examples table and accompanying certificates; sections/08_exact_classification_examples.tex, sec:exact_examples; tab:selection_exact.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.exact_matched_geometry_example : ExactMatchedExampleClaim := by sorry
