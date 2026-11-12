-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_oneShotPostprocess_evenBranch
-- name    : QEC.Distillation.PhaseInjection.oneShotPostprocess_evenBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:13:12.617205+00:00
-- url     : https://prove2.me/theorems/7fde1bc1-df05-4e55-a38b-e26a086364a2
-- title:
--   Phase Injection: one Shot Postprocess even Branch
-- statement:
--   The existing even branch density is processed by the literal XOR/discard channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L159-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L159-L164

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct

theorem QEC.Distillation.PhaseInjection.oneShotPostprocess_evenBranch
    (psi : TwoQubit.TwoQubitSpace) (h : 0 < TwoQubit.zzEvenWeight psi) :
    oneShotPostprocess.mapDensity (TwoQubit.zzEvenBranchDensity psi h) =
      TwoQubit.zzEvenBranchFirstDensity psi h := by sorry
