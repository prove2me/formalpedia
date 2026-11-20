-- Prove2me | Theorems.Thm_QEC_Distillation_hActualRawTree_retainsComplementLeaf
-- name    : QEC.Distillation.hActualRawTree_retainsComplementLeaf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T21:33:24.798175+00:00
-- url     : https://prove2.me/theorems/a2760940-1f26-4e88-8b5b-b21531371b16
-- title:
--   Distillation: h Actual Raw Tree retains Complement Leaf
-- statement:
--   Away from the immediate target and with a nonzero phase budget, the raw H
--   tree is literally the appended positive and complementary negative branches.
--   This is a conditional structural statement because `target = 0` or a zero
--   budget legitimately stops before either branch is attempted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L1294-L1306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L1294-L1306

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

theorem QEC.Distillation.hActualRawTree_retainsComplementLeaf
    (h : DensityOperator QubitSpace) (target : ZMod 8) (blocks : Nat)
    (rho : DensityOperator QubitSpace)
    (htarget : (0 : ZMod 8) ≠ target) (hblocks : 0 < blocks) :
    hActualRawTree h target blocks rho =
      hRetry h target (8 * blocks - 1) 1 ({.h} : ResourceLedger BK05ResourceToken)
        [true] (hStepRaw h true rho.toOperator)
      ++
      hRetry h target (8 * blocks - 1) (-1) ({.h} : ResourceLedger BK05ResourceToken)
        [false] (hStepRaw h false rho.toOperator) := by sorry
