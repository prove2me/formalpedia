-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_vonNeumannEntropy_le_card_mul_log_uniformDimension
-- name    : QEC.Semantics.QuditSubsystem.vonNeumannEntropy_le_card_mul_log_uniformDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:15:36.894396+00:00
-- url     : https://prove2.me/theorems/50bba228-bd59-49a2-bede-61dca73944e0
-- title:
--   Qudit Subsystem: von Neumann Entropy le card mul log uniform Dimension
-- statement:
--   Maximum entropy on a selected qudit region under an explicit uniform local bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L220-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L220-L225

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
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι -> Nat}

theorem QEC.Semantics.QuditSubsystem.vonNeumannEntropy_le_card_mul_log_uniformDimension (S : QuditSubsystem q)
    (hq : forall i, 0 < q i) (D : Nat)
    (hD : forall i, i ∈ S.selected -> q i <= D) (rho : DensityOperator S.selectedSystem) :
    rho.vonNeumannEntropy <= (S.selected.card : Real) * Real.logb 2 (D : Real) := by sorry
