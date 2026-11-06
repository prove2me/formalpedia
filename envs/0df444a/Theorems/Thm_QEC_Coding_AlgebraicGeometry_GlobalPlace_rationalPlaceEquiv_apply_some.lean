-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:12.031199+00:00
-- url     : https://prove2.me/theorems/dcb9e1c7-1e48-4149-b4f6-d04702e6275d
-- title:
--   Global Place: rational Place Equiv apply some
-- statement:
--   The Global Place construction uses the rational Place Equiv apply some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncPlaceClassification.lean#L136-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncPlaceClassification.lean#L136-L138

import Mathlib.NumberTheory.RatFunc.Ostrowski
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    rationalPlaceEquiv (k := k) (some p) = rationalAdic p := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
