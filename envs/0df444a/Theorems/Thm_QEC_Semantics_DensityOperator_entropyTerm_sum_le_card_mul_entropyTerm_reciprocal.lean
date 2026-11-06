-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_entropyTerm_sum_le_card_mul_entropyTerm_reciprocal
-- name    : QEC.Semantics.DensityOperator.entropyTerm_sum_le_card_mul_entropyTerm_reciprocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:00.314507+00:00
-- url     : https://prove2.me/theorems/05ff9948-f58b-4958-9ebf-ce8430bffbeb
-- title:
--   Density Operator: entropy Term sum le card mul entropy Term reciprocal
-- statement:
--   Finite Jensen for base-two entropy with uniform weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L47-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L47-L70

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

theorem QEC.Semantics.DensityOperator.entropyTerm_sum_le_card_mul_entropyTerm_reciprocal (n : Nat) (hn : 0 < n)
    (p : Fin n -> Real) (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (∑ i, entropyTerm (p i)) <= (n : Real) * entropyTerm ((n : Real)⁻¹) := by sorry
