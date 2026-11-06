-- Prove2me | Theorems.Thm_QEC_Semantics_positivePart_sub_negativePart
-- name    : QEC.Semantics.positivePart_sub_negativePart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:53.773191+00:00
-- url     : https://prove2.me/theorems/396ac93d-059a-476e-9774-b9ca21d56346
-- title:
--   Semantics: positive Part sub negative Part
-- statement:
--   A self-adjoint operator is its positive part minus its negative part.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L250-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L250-L256

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.positivePart_sub_negativePart (A : Operator H) (hA : A.IsSymmetric) :
    positivePart A - negativePart A = A := by sorry
