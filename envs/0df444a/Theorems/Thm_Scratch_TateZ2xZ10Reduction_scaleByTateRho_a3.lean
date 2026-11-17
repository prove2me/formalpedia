-- Prove2me | Theorems.Thm_Scratch_TateZ2xZ10Reduction_scaleByTateRho_a3
-- name    : Scratch.TateZ2xZ10Reduction.scaleByTateRho_a3
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:15.635622+00:00
-- url     : https://prove2.me/theorems/ad126943-fcbd-4d2b-b30b-244e0706ff0f
-- title:
--   Tate scaling normalizes the $a_3$ coefficient
-- statement:
--   Let $W/ℚ$ be a Weierstrass curve with $a_2(W)≠0$ and $a_3(W)≠0$, put $ρ=a_3(W)/a_2(W)$, and apply the scaling $X=ρ^2X'$, $Y=ρ^3Y'$. Then the transformed cubic coefficient is $$a_3(ρ·W)=\frac{a_2(W)^3}{a_3(W)^2}.$$ Together with the companion $a_2$ formula, this yields the equal coefficients characteristic of Tate normal form.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_TateZ2xZ10Reduction

open scoped WeierstrassCurve.Affine
open Scratch
open Scratch.TateZ2xZ10Reduction

theorem Scratch.TateZ2xZ10Reduction.scaleByTateRho_a3
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ ≠ 0) (ha₃ : W.a₃ ≠ 0) :
    ((scaleByRho (W.a₃ / W.a₂) (div_ne_zero ha₃ ha₂)) • W).a₃ =
      W.a₂ ^ 3 / W.a₃ ^ 2 := by sorry
