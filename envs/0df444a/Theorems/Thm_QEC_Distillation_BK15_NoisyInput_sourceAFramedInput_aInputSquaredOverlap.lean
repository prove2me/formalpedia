-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceAFramedInput_aInputSquaredOverlap
-- name    : QEC.Distillation.BK15.NoisyInput.sourceAFramedInput_aInputSquaredOverlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:58:58.125563+00:00
-- url     : https://prove2.me/theorems/5218fec5-4339-4ec7-9f95-f24a2debb7d4
-- title:
--   Noisy Input: source AFramed Input a Input Squared Overlap
-- statement:
--   The Noisy Input construction uses the source AFramed Input a Input Squared Overlap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L682-L699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L682-L699

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

theorem QEC.Distillation.BK15.NoisyInput.sourceAFramedInput_aInputSquaredOverlap (rho : DensityOperator QubitSpace) :
    aInputSquaredOverlap (sourceAFramedInput rho) = hFidelity rho ^ 2 := by sorry
