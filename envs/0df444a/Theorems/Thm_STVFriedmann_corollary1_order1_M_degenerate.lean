-- Prove2me | Theorems.Thm_STVFriedmann_corollary1_order1_M_degenerate
-- name    : STVFriedmann.corollary1_order1_M_degenerate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T01:56:43.33009+00:00
-- url     : https://prove2.me/theorems/be51436b-9a7a-4d53-b3cf-71cee06a855a
-- title:
--   STV ODE of order 1: M is a degenerate stable rest point
-- statement:
--   Let $DF_1(M)$ be the Jacobian of the order-1 STV ODE (2.34)–(2.35) at the Minkowski rest point $M=(0,1)$. Then:
--
--   1. $\boldsymbol R_M=(0,1)^T$ is an eigenvector with eigenvalue $\lambda_M=-1$;
--   2. every (real) eigenpair $(\mu, v)$, $v\ne0$, of $DF_1(M)$ has $\mu=-1$ and $v$ a multiple of $\boldsymbol R_M$.
--
--   That is, $M$ is a degenerate stable rest point with one eigenvalue and one eigenvector.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 12, Corollary 1 eq. (2.28); p. 16 (M has repeated eigenvalue -1 and single eigenvector R_M = (0,1)^T at n = 1)

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Corollary 1 (n = 1), (2.28): at `M = (0,1)` the Jacobian of the order-1 STV ODE has the
single eigenvalue `-1` with the single eigenvector direction `R_M = (0, 1)`. -/
theorem corollary1_order1_M_degenerate :
    fderiv ℝ stvField1 restM1 ![0, 1] = (-1 : ℝ) • ![0, 1] ∧
    ∀ (μ : ℝ) (v : Fin 2 → ℝ), v ≠ 0 → fderiv ℝ stvField1 restM1 v = μ • v →
      μ = -1 ∧ ∃ c : ℝ, v = c • ![0, 1] := by sorry

end STVFriedmann
