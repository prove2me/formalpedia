-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_trivialOnConstants
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.trivialOnConstants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:09:04.68708+00:00
-- url     : https://prove2.me/theorems/a12902f8-1e8d-4b45-a5ea-803124419e96
-- title:
--   Global Place: trivial On Constants
-- statement:
--   A global place is trivial on the supplied finite constant field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L47-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L47-L48

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.trivialOnConstants (P : GlobalPlace k F) : P.valuation.IsTrivialOn k := by sorry
