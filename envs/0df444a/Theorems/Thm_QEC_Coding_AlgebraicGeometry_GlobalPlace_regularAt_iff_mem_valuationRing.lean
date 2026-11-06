-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.regularAt_iff_mem_valuationRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:14.521224+00:00
-- url     : https://prove2.me/theorems/ddc66e0f-19c3-4364-9e1e-6a4312013911
-- title:
--   Global Place: regular At iff mem valuation Ring
-- statement:
--   The Global Place construction uses the regular At iff mem valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L117-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L117-L119

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.regularAt_iff_mem_valuationRing (P : GlobalPlace k F) (f : F) :
    RegularAt P f ↔ f ∈ valuationRing P := by sorry
