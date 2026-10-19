-- Prove2me | Theorems.Thm_STVFriedmann_corollary1_order2_rest_points
-- name    : STVFriedmann.corollary1_order2_rest_points
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T01:57:09.624095+00:00
-- url     : https://prove2.me/theorems/7b8b2767-820b-4d66-84ac-48df8b6fa879
-- title:
--   STV ODE of order 2: rest points U, M, SM
-- statement:
--   Consider the **STV ODE of order $n=2$**, equations (2.48)–(2.51), in the unknowns $(z_2,w_0,z_4,w_2)$:
--
--   $$
--   \begin{aligned}
--   \bar t\dot z_2 &= 2z_2-3z_2w_0, &\qquad \bar t\dot w_0 &= -\tfrac16 z_2+w_0-w_0^2,\\
--   \bar t\dot z_4 &= \tfrac5{12}z_2^2w_0+4z_4-5w_0z_4-5z_2w_2, &\qquad
--   \bar t\dot w_2 &= -\tfrac1{24}z_2^2+\tfrac14 z_2w_0^2-\tfrac1{10}z_4+3w_2-4w_0w_2 .
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   U=(0,0,0,0),\qquad M=(0,1,0,0),\qquad SM=\left(\tfrac43,\tfrac23,\tfrac{40}{27},\tfrac29\right)
--   $$
--
--   are rest points of this system.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 17, eqs. (2.48)-(2.51) and the following paragraph; p. 12, Corollary 1 eq. (2.27)

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Section 2.7 / Corollary 1 (n = 2): `U = 0`, `M = (0,1,0,0)` and
`SM = (4/3, 2/3, 40/27, 2/9)` are rest points of the order-2 STV ODE (2.48)–(2.51). -/
theorem corollary1_order2_rest_points :
    stvField2 restU2 = 0 ∧ stvField2 restM2 = 0 ∧ stvField2 restSM2 = 0 := by sorry

end STVFriedmann
