-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearGroup_commutator_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinearGroup_commutator_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:42:51.429214+00:00
-- url     : https://prove2.me/theorems/5b55d153-cfed-418a-b33a-755fcceb80e7
-- title:
--   Cartwright Steger: special Linear Group commutator eq top
-- statement:
--   In matrix ranks three and four the special linear group is perfect.  The
--   proof uses Gaussian transvection induction, the explicit diagonal
--   factorizations from congruence lifting, and the Steinberg commutator relation
--   above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L121-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L121-L165

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinearGroup_commutator_eq_top
    {K : Type*} [Field K] (r : Rank) :
    commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K) = ⊤ := by sorry
