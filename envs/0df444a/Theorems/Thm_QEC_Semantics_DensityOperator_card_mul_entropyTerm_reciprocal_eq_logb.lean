-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_card_mul_entropyTerm_reciprocal_eq_logb
-- name    : QEC.Semantics.DensityOperator.card_mul_entropyTerm_reciprocal_eq_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:06:28.260189+00:00
-- url     : https://prove2.me/theorems/37cfe3c2-f9e6-4a10-9a22-c20a153922a8
-- title:
--   Density Operator: card mul entropy Term reciprocal eq logb
-- statement:
--   The uniform Jensen right-hand side is exactly the base-two logarithm of the cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L73-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L73-L76

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

theorem QEC.Semantics.DensityOperator.card_mul_entropyTerm_reciprocal_eq_logb (n : Nat) (hn : 0 < n) :
    (n : Real) * entropyTerm ((n : Real)⁻¹) = Real.logb 2 (n : Real) := by sorry
