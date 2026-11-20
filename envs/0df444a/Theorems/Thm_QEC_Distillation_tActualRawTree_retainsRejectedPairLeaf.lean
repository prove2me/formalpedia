-- Prove2me | Theorems.Thm_QEC_Distillation_tActualRawTree_retainsRejectedPairLeaf
-- name    : QEC.Distillation.tActualRawTree_retainsRejectedPairLeaf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T21:31:53.527958+00:00
-- url     : https://prove2.me/theorems/d53bae7f-9334-4b3e-ad91-87d5a0d104cf
-- title:
--   Distillation: t Actual Raw Tree retains Rejected Pair Leaf
-- statement:
--   If the first physical T phase attempt is reached, the bounded supplier's
--   all-rejected outcome becomes a retained `tPairExhausted` leaf.  The target and
--   zero-block cases are deliberately excluded because they stop before a pair is
--   requested.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L1414-L1441
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L1414-L1441

import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality
set_option autoImplicit false
noncomputable section
universe u v
open QEC
open QEC.Distillation
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open GeneratedUniversality
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators Matrix.Norms.Elementwise
open AdaptiveIdealClifford PhaseInjection

theorem QEC.Distillation.tActualRawTree_retainsRejectedPairLeaf
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace)
    (htarget : (0 : ZMod 12) ≠ target) (hblocks : 0 < blocks) :
    pairAttempts = 0 ∨
      (0 < pairAttempts →
        ∃ leaf ∈ tActualRawTree t pairAttempts target blocks rho,
          leaf.kind = .tPairExhausted ∧
          leaf.ledger.card = 2 * pairAttempts ∧
          List.replicate pairAttempts false = leaf.history ∧ false ∈ leaf.history) := by sorry
