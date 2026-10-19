-- Prove2me | Theorems.Thm_STVFriedmann_corollary1_order2_M_stable
-- name    : STVFriedmann.corollary1_order2_M_stable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T01:58:22.95443+00:00
-- url     : https://prove2.me/theorems/44ee2fb3-5556-4773-ab28-31d29de70e78
-- title:
--   STV ODE of order 2: M is a stable rest point with the single eigenvalue -1
-- statement:
--   Let $DF_2(M)$ be the Jacobian of the order-2 STV ODE (2.48)–(2.51) at the Minkowski rest point $M=(0,1,0,0)$. Then:
--
--   1. $\boldsymbol R_M=(0,1,0,1)^T$ satisfies $DF_2(M)\boldsymbol R_M=-\boldsymbol R_M$;
--   2. $\lambda_M=-1$ is the only real eigenvalue of $DF_2(M)$.
--
--   So $M$ is a degenerate stable rest point of the order-2 system.
--
--   **Formalization Note** Corollary 1 also states that $\boldsymbol R_M$ is the *only* eigenvector. For the explicit system (2.48)–(2.51) this is not correct as stated: at $M$ the eigenspace for $-1$ is spanned by $(0,1,0,0)^T$ and $(0,0,0,1)^T$, so it is two-dimensional. This statement therefore keeps only the parts of (2.28) that hold for (2.48)–(2.51).
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 12, Corollary 1 eq. (2.28); p. 16 (M is a degenerate stable rest point at every order n >= 1 with eigenvalue -1)

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Corollary 1 (n = 2), (2.28): at `M = (0,1,0,0)` the vector `R_M = (0,1,0,1)` is an
eigenvector of the Jacobian of the order-2 STV ODE with eigenvalue `-1`, and `-1` is the only
(real) eigenvalue. -/
theorem corollary1_order2_M_stable :
    fderiv ℝ stvField2 restM2 ![0, 1, 0, 1] = (-1 : ℝ) • ![0, 1, 0, 1] ∧
    ∀ (μ : ℝ) (v : Fin 4 → ℝ), v ≠ 0 → fderiv ℝ stvField2 restM2 v = μ • v → μ = -1 := by
  sorry

end STVFriedmann
