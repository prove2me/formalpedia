-- Prove2me | Theorems.Thm_STVFriedmann_corollary1_order1_rest_points
-- name    : STVFriedmann.corollary1_order1_rest_points
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T01:55:51.289983+00:00
-- url     : https://prove2.me/theorems/2f2ada21-75fb-49e6-ac91-146e9681ad19
-- title:
--   STV ODE of order 1: rest points U, M, SM
-- statement:
--   Consider the **STV ODE of order $n=1$** (equations (2.34)–(2.35)) for the leading-order density and velocity coefficients $(z_2, w_0)$ of a smooth, spherically symmetric, pressureless solution of the Einstein–Euler equations in self-similar variables:
--
--   $$
--   \bar t\,\dot z_2 = 2z_2 - 3z_2w_0,\qquad \bar t\,\dot w_0 = -\tfrac16 z_2 + w_0 - w_0^2 .
--   $$
--
--   Then the three points
--
--   $$
--   U=(0,0),\qquad M=(0,1),\qquad SM=\left(\tfrac43,\tfrac23\right)
--   $$
--
--   are rest points of this system, i.e. the right-hand side vanishes at each of them.
--
--   Here $M$ represents Minkowski spacetime and $SM$ the critical ($k=0$) Friedmann spacetime ("Standard Model"); $U$ is the unstable rest point at the origin.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 12, Corollary 1 eq. (2.27) and Section 2.4 (text after (2.35))

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Corollary 1 / Section 2.4 (n = 1): `U = (0,0)`, `M = (0,1)` and `SM = (4/3, 2/3)` are
rest points of the order-1 STV ODE (2.34)–(2.35). -/
theorem corollary1_order1_rest_points :
    stvField1 restU1 = 0 ∧ stvField1 restM1 = 0 ∧ stvField1 restSM1 = 0 := by sorry

end STVFriedmann
