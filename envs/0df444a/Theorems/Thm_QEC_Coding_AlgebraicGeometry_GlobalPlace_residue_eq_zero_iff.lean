-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.residue_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:46.945203+00:00
-- url     : https://prove2.me/theorems/e9877157-3f66-4496-aaa3-a643fe3a59a0
-- title:
--   Global Place: residue eq zero iff
-- statement:
--   Integral elements reduce to zero exactly when they lie in the maximal ideal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L104-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L104-L106

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.residue_eq_zero_iff (P : GlobalPlace k F) (f : valuationRing P) :
    residue P f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (valuationRing P) := by sorry
