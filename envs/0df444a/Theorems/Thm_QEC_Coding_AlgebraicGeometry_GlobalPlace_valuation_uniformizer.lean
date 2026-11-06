-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation_uniformizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:09:10.560646+00:00
-- url     : https://prove2.me/theorems/89d4b7b9-abda-4cdf-9a36-0ab385b019d8
-- title:
--   Global Place: valuation uniformizer
-- statement:
--   The chosen uniformizer has valuation `exp (-1)`, exhibiting the discrete
--   integer normalization without storing any divisor or Riemann--Roch law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L56-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L56-L58

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation_uniformizer (P : GlobalPlace k F) :
    P.valuation P.uniformizer = WithZero.exp (-1 : ℤ) := by sorry
