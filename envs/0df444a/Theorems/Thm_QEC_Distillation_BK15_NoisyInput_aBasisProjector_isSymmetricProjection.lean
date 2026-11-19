-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisProjector_isSymmetricProjection
-- name    : QEC.Distillation.BK15.NoisyInput.aBasisProjector_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:07:21.886622+00:00
-- url     : https://prove2.me/theorems/0e9e61bb-a52b-4590-880c-23f1d87794bd
-- title:
--   Noisy Input: a Basis Projector is Symmetric Projection
-- statement:
--   The Noisy Input construction uses the a Basis Projector is Symmetric Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L367-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L367-L372

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

theorem QEC.Distillation.BK15.NoisyInput.aBasisProjector_isSymmetricProjection
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) :
    (aBasisProjector outcome).IsSymmetricProjection := by sorry
