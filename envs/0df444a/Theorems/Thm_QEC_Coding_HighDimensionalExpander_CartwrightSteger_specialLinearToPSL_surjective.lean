-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearToPSL_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinearToPSL_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:42:58.464174+00:00
-- url     : https://prove2.me/theorems/e4d99b32-c95c-4d67-8550-a664292d4f80
-- title:
--   Cartwright Steger: special Linear To PSL surjective
-- statement:
--   The Cartwright Steger construction uses the special Linear To PSL surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L179-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L179-L186

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinearToPSL_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (specialLinearToPSL P r level) := by sorry
