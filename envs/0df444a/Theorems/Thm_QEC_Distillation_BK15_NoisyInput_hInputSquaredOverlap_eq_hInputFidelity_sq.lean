-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hInputSquaredOverlap_eq_hInputFidelity_sq
-- name    : QEC.Distillation.BK15.NoisyInput.hInputSquaredOverlap_eq_hInputFidelity_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:58:39.344085+00:00
-- url     : https://prove2.me/theorems/4a7034e5-08a0-4216-9cbd-1d129df4c517
-- title:
--   Noisy Input: h Input Squared Overlap eq h Input Fidelity sq
-- statement:
--   The Noisy Input construction uses the h Input Squared Overlap eq h Input Fidelity sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L610-L616
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L610-L616

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

theorem QEC.Distillation.BK15.NoisyInput.hInputSquaredOverlap_eq_hInputFidelity_sq
    (rho : DensityOperator QubitSpace) :
    hInputSquaredOverlap rho = hInputFidelity rho ^ 2 := by sorry
