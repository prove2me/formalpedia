-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_oneShotPostprocess_oddBranch
-- name    : QEC.Distillation.PhaseInjection.oneShotPostprocess_oddBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:13:51.564924+00:00
-- url     : https://prove2.me/theorems/df0e72fb-fd4b-4b5c-9a3d-24e633bb4d24
-- title:
--   Phase Injection: one Shot Postprocess odd Branch
-- statement:
--   The existing odd branch density is processed by the literal XOR/discard channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L167-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L167-L172

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

theorem QEC.Distillation.PhaseInjection.oneShotPostprocess_oddBranch
    (psi : TwoQubit.TwoQubitSpace) (h : 0 < TwoQubit.zzOddWeight psi) :
    oneShotPostprocess.mapDensity (TwoQubit.zzOddBranchDensity psi h) =
      TwoQubit.zzOddBranchFirstDensity psi h := by sorry
