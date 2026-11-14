-- Prove2me | Theorems.Thm_PGDRevision20261113_exact_asymmetric_interior_geometry_example
-- name    : PGDRevision20261113.exact_asymmetric_interior_geometry_example
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:08:05.612549+00:00
-- url     : https://prove2.me/theorems/dd5937d9-b00d-476e-9484-a2c735ba735d
-- title:
--   An exact interior optimum with only two active signed states
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
--   For $A(t)=9+8t+7t^2$ and $\lambda=20736/625$, the unique minimizing pair and exact rate are
--   $$
--   (c_*,p_*)=(1/2,768/(25\sqrt{10})),\qquad \rho_*=5/66.
--   $$
--   At this pair the global envelope $|E(t)|\le\rho_*$ holds throughout $I$. The only states with $|E|=5/66$ are $-3/5$ and $3/5$, with signs $+$ and $-$. Thus there are no three alternating contacts at three distinct ordered features.
--
--   For every finite $N\ge1$, the optimal value is $\Omega_N=\rho_*^{2N}$, and the same pair uniquely minimizes this criterion. The admissibility conditions, global envelope, exact contacts, uniqueness, and finite-horizon assertions are all included in the formal statement.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [asymmetric interior algebraic factorization](https://prove2.me/theorems/0b0aafd3-0bd5-43e8-9838-a2bcc22354a2) · [asymmetric interior coefficient certificate](https://prove2.me/theorems/ba90c632-0e54-482c-b43c-5bc862aa020d)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 8, exact classification examples table and accompanying certificates; sections/08_exact_classification_examples.tex, sec:exact_examples; tab:selection_exact.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.exact_asymmetric_interior_geometry_example : ExactAsymmetricInteriorExampleClaim := by sorry
