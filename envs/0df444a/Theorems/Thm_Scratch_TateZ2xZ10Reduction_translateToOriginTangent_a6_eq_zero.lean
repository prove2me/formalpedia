-- Prove2me | Theorems.Thm_Scratch_TateZ2xZ10Reduction_translateToOriginTangent_a6_eq_zero
-- name    : Scratch.TateZ2xZ10Reduction.translateToOriginTangent_a6_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:38.383035+00:00
-- url     : https://prove2.me/theorems/6364ed08-7bd2-4471-acd7-6bee1aac9cf9
-- title:
--   Translation of a curve point kills the constant coefficient
-- statement:
--   Let $W/ℚ$ be a Weierstrass curve and let $(x_0,y_0)∈ℚ^2$ satisfy its affine Weierstrass equation. Let $τ$ be the translation-and-tangent-shear sending $(x_0,y_0)$ to $(0,0)$. Then $$a_6(τ·W)=0.$$ This is the constant-term normalization required for Tate normal form.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_TateZ2xZ10Reduction

open scoped WeierstrassCurve.Affine
open Scratch
open Scratch.TateZ2xZ10Reduction

theorem Scratch.TateZ2xZ10Reduction.translateToOriginTangent_a6_eq_zero
    (W : WeierstrassCurve ℚ) {x₀ y₀ : ℚ}
    (hP : WeierstrassCurve.Affine.Equation W x₀ y₀) :
    ((translateToOriginTangent W x₀ y₀) • W).a₆ = 0 := by sorry
