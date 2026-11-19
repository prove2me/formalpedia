-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceAFramedInput_error_eq_one_sub_hFidelity_sq
-- name    : QEC.Distillation.BK15.NoisyInput.sourceAFramedInput_error_eq_one_sub_hFidelity_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:58:58.13689+00:00
-- url     : https://prove2.me/theorems/ee34cfac-0544-4472-8f77-b6ddf01641eb
-- title:
--   Noisy Input: source AFramed Input error eq one sub h Fidelity sq
-- statement:
--   Once the H frame is transported to A, the error is exactly `1 - F_H²`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L702-L705
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L702-L705

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

theorem QEC.Distillation.BK15.NoisyInput.sourceAFramedInput_error_eq_one_sub_hFidelity_sq
    (rho : DensityOperator QubitSpace) :
    aInputError (sourceAFramedInput rho) = 1 - hFidelity rho ^ 2 := by sorry
