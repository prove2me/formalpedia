-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisDephasing_apply
-- name    : QEC.Distillation.BK15.NoisyInput.aBasisDephasing_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:07:20.372274+00:00
-- url     : https://prove2.me/theorems/71540732-5cac-429f-abff-ec7b315c60a0
-- title:
--   Noisy Input: a Basis Dephasing apply
-- statement:
--   The source A-basis dephasing, expressed as a finite projective channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L481-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L481-L498

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.BK15.NoisyInput.aBasisDephasing_apply (A : Operator QubitSpace) :
    aBasisDephasing A =
      (1 / 2 : Complex) •
        (A + aBasisObservable.comp (A.comp aBasisObservable)) := by sorry
