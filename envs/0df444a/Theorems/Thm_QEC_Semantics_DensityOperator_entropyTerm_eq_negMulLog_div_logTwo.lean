-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_entropyTerm_eq_negMulLog_div_logTwo
-- name    : QEC.Semantics.DensityOperator.entropyTerm_eq_negMulLog_div_logTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:05.805752+00:00
-- url     : https://prove2.me/theorems/67a51598-b9e2-4131-9483-9bca67716809
-- title:
--   Density Operator: entropy Term eq neg Mul Log div log Two
-- statement:
--   The base-two entropy contribution is a positive rescaling of `negMulLog`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L30-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L30-L37

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.entropyTerm_eq_negMulLog_div_logTwo (x : Real) :
    entropyTerm x = (Real.log 2)⁻¹ * Real.negMulLog x := by sorry
