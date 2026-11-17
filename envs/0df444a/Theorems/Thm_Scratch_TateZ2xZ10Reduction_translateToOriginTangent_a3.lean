-- Prove2me | Theorems.Thm_Scratch_TateZ2xZ10Reduction_translateToOriginTangent_a3
-- name    : Scratch.TateZ2xZ10Reduction.translateToOriginTangent_a3
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:25.715445+00:00
-- url     : https://prove2.me/theorems/19a46cf1-918a-4762-9511-7d155f4187c2
-- title:
--   The translated Weierstrass coefficient $a_3$
-- statement:
--   Let $W/ℚ$ be a Weierstrass curve with coefficients $a_1,…,a_6$, and let $x_0,y_0∈ℚ$. Let $τ$ be the variable change that translates $(x_0,y_0)$ to the origin and shears by the tangent slope, with scale $1$, horizontal translation $x_0$, and vertical translation $y_0$. Then the transformed coefficient satisfies $$a_3(τ·W)=a_3(W)+a_1(W)x_0+2y_0.$$ This is one of the coefficient identities used to reach Tate normal form.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_TateZ2xZ10Reduction

open scoped WeierstrassCurve.Affine
open Scratch
open Scratch.TateZ2xZ10Reduction

@[simp]
theorem Scratch.TateZ2xZ10Reduction.translateToOriginTangent_a3 (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₃ =
      W.a₃ + W.a₁ * x₀ + 2 * y₀ := by sorry
