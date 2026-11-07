-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialTransvection_mem_commutator
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialTransvection_mem_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:43:22.667935+00:00
-- url     : https://prove2.me/theorems/96b488e4-a1da-438b-9e50-ca8b8a794f2f
-- title:
--   Cartwright Steger: special Transvection mem commutator
-- statement:
--   Every elementary transvection in matrix rank at least three belongs to
--   the commutator subgroup of the special linear group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L105-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L105-L115

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialTransvection_mem_commutator
    {K : Type*} [Field K] (r : Rank)
    (i j : Fin r.matrixRank) (hij : i ≠ j) (c : K) :
    specialTransvection i j hij c ∈
      commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K) := by sorry
