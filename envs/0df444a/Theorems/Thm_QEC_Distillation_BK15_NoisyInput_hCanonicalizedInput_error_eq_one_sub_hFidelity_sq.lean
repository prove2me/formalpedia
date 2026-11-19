-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hCanonicalizedInput_error_eq_one_sub_hFidelity_sq
-- name    : QEC.Distillation.BK15.NoisyInput.hCanonicalizedInput_error_eq_one_sub_hFidelity_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:07:42.826194+00:00
-- url     : https://prove2.me/theorems/ba94c866-2658-4d98-806f-007afa0b4078
-- title:
--   Noisy Input: h Canonicalized Input error eq one sub h Fidelity sq
-- statement:
--   Canonicalization identifies the operational error with `1 - F_H²`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L636-L640
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L636-L640

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

theorem QEC.Distillation.BK15.NoisyInput.hCanonicalizedInput_error_eq_one_sub_hFidelity_sq
    (rho : DensityOperator QubitSpace) :
    hInputError (hCanonicalizedInput rho) = 1 - hFidelity rho ^ 2 := by sorry
