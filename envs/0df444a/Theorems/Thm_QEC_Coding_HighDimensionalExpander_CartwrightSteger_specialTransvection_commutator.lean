-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialTransvection_commutator
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialTransvection_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:43:21.439142+00:00
-- url     : https://prove2.me/theorems/fe95bc34-a7d3-47a5-a992-06a194f41f32
-- title:
--   Cartwright Steger: special Transvection commutator
-- statement:
--   The Steinberg commutator relation, in the exact bundled form needed for
--   the commutator subgroup of `SL`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L38-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L38-L101

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialTransvection_commutator
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (i j k : n) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (c : K) :
    ⁅specialTransvection i k hik c,
        specialTransvection k j hkj 1⁆ =
      specialTransvection i j hij c := by sorry
