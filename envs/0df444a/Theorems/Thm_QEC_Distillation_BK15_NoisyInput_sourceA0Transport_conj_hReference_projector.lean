-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceA0Transport_conj_hReference_projector
-- name    : QEC.Distillation.BK15.NoisyInput.sourceA0Transport_conj_hReference_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:59:01.344588+00:00
-- url     : https://prove2.me/theorems/cd933264-f191-46df-85fd-8bf08a7d8c5e
-- title:
--   Noisy Input: source A0 Transport conj h Reference projector
-- statement:
--   The H reference projector transported by the literal `K†`-then-`H` route
--   is exactly the positive source-A projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L646-L660
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L646-L660

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

theorem QEC.Distillation.BK15.NoisyInput.sourceA0Transport_conj_hReference_projector :
    sourceA0Transport.conjOperator (hProjector hReference) =
      aBasisProjector .positive := by sorry
