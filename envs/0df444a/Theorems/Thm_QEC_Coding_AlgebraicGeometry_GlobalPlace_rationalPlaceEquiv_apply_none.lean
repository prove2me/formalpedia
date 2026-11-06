-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:19:47.588356+00:00
-- url     : https://prove2.me/theorems/ed9295f0-6bdd-401f-936f-28f3a16b2e37
-- title:
--   Global Place: rational Place Equiv apply none
-- statement:
--   The Global Place construction uses the rational Place Equiv apply none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncPlaceClassification.lean#L132-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncPlaceClassification.lean#L132-L133

import Mathlib.NumberTheory.RatFunc.Ostrowski
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none :
    rationalPlaceEquiv (k := k) none = rationalInfinity k := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
