-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hCanonicalizer_conj_hProjector
-- name    : QEC.Distillation.BK15.NoisyInput.hCanonicalizer_conj_hProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:58:58.445561+00:00
-- url     : https://prove2.me/theorems/77fdaeb6-2305-40ec-809a-b631b2449243
-- title:
--   Noisy Input: h Canonicalizer conj h Projector
-- statement:
--   The Noisy Input construction uses the h Canonicalizer conj h Projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L618-L626
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L618-L626

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

theorem QEC.Distillation.BK15.NoisyInput.hCanonicalizer_conj_hProjector (d : HDirection) :
    (hCanonicalizer d).conjOperator (hProjector d) = hProjector hReference := by sorry
