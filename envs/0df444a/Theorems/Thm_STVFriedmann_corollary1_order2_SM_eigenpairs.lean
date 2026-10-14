-- Prove2me | Theorems.Thm_STVFriedmann_corollary1_order2_SM_eigenpairs
-- name    : STVFriedmann.corollary1_order2_SM_eigenpairs
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T01:57:55.623302+00:00
-- url     : https://prove2.me/theorems/f6df7eca-54dc-4ef3-93ab-027dc7d9a122
-- title:
--   STV ODE of order 2: eigenpairs of the saddle SM
-- statement:
--   Let $DF_2(SM)$ be the Jacobian of the order-2 STV ODE (2.48)–(2.51) at $SM=(\tfrac43,\tfrac23,\tfrac{40}{27},\tfrac29)$. Then $DF_2(SM)\boldsymbol R=\lambda\boldsymbol R$ for each of the four pairs
--
--   $$
--   \begin{aligned}
--   \lambda_{A1}&=\tfrac23, & \boldsymbol R_{A1}&=\left(-9,\tfrac32,-\tfrac{10}3,-1\right)^T,\\
--   \lambda_{B1}&=-1, & \boldsymbol R_{B1}&=\left(4,1,\tfrac{80}9,1\right)^T,\\
--   \lambda_{A2}&=\tfrac43, & \boldsymbol R_{A2}&=\left(0,0,-10,1\right)^T,\\
--   \lambda_{B2}&=-\tfrac13, & \boldsymbol R_{B2}&=\left(0,0,\tfrac{20}3,1\right)^T.
--   \end{aligned}
--   $$
--
--   Hence at order $2$ the rest point $SM$ is hyperbolic, with two unstable directions ($\tfrac23,\tfrac43$) and two stable directions ($-1,-\tfrac13$).
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 12, Corollary 1 eqs. (2.29)-(2.33)

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Corollary 1, (2.30)–(2.33): the four eigenpairs of the Jacobian of the order-2 STV ODE
at `SM`. -/
theorem corollary1_order2_SM_eigenpairs :
    fderiv ℝ stvField2 restSM2 ![-9, 3 / 2, -10 / 3, -1] =
        (2 / 3 : ℝ) • ![-9, 3 / 2, -10 / 3, -1] ∧
    fderiv ℝ stvField2 restSM2 ![4, 1, 80 / 9, 1] = (-1 : ℝ) • ![4, 1, 80 / 9, 1] ∧
    fderiv ℝ stvField2 restSM2 ![0, 0, -10, 1] = (4 / 3 : ℝ) • ![0, 0, -10, 1] ∧
    fderiv ℝ stvField2 restSM2 ![0, 0, 20 / 3, 1] = (-1 / 3 : ℝ) • ![0, 0, 20 / 3, 1] := by
  sorry

end STVFriedmann
