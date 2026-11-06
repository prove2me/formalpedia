-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_finite_jensen_entropyTerm_sum_le_logb_card
-- name    : QEC.Semantics.DensityOperator.finite_jensen_entropyTerm_sum_le_logb_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:13.240581+00:00
-- url     : https://prove2.me/theorems/298027b4-98a0-4e4a-a476-0d64cdbefb13
-- title:
--   Density Operator: finite jensen entropy Term sum le logb card
-- statement:
--   A finite probability vector has entropy at most the logarithm of its cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L79-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L79-L85

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

theorem QEC.Semantics.DensityOperator.finite_jensen_entropyTerm_sum_le_logb_card (n : Nat) (hn : 0 < n)
    (p : Fin n -> Real) (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (∑ i, entropyTerm (p i)) <= Real.logb 2 (n : Real) := by sorry
