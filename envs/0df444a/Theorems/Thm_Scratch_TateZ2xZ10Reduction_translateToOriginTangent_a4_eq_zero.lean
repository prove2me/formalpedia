-- Prove2me | Theorems.Thm_Scratch_TateZ2xZ10Reduction_translateToOriginTangent_a4_eq_zero
-- name    : Scratch.TateZ2xZ10Reduction.translateToOriginTangent_a4_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:31.8658+00:00
-- url     : https://prove2.me/theorems/09b72ad7-83a5-4957-9ea8-eb17042b9d3a
-- title:
--   The tangent shear kills the $a_4$ coefficient
-- statement:
--   Let $W/ℚ$ be a Weierstrass curve and let $x_0,y_0∈ℚ$ satisfy $2y_0+a_1(W)x_0+a_3(W)≠0$, so the prescribed tangent slope is defined. If $τ$ is the corresponding translation-and-tangent-shear, then $$a_4(τ·W)=0.$$ This removes the linear $X$ term in the reduction toward Tate normal form; no hypothesis that $(x_0,y_0)$ lies on $W$ is part of this statement.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_TateZ2xZ10Reduction

open scoped WeierstrassCurve.Affine
open Scratch
open Scratch.TateZ2xZ10Reduction

theorem Scratch.TateZ2xZ10Reduction.translateToOriginTangent_a4_eq_zero
    (W : WeierstrassCurve ℚ) {x₀ y₀ : ℚ}
    (hden : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0) :
    ((translateToOriginTangent W x₀ y₀) • W).a₄ = 0 := by sorry
