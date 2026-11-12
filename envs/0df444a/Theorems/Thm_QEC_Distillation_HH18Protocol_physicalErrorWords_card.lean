-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_physicalErrorWords_card
-- name    : QEC.Distillation.HH18Protocol.physicalErrorWords_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:57:52.517364+00:00
-- url     : https://prove2.me/theorems/de0409a4-7f98-41ea-af4c-f74dd1df7ad0
-- title:
--   HH18 Protocol: physical Error Words card
-- statement:
--   The HH18 Protocol construction uses the physical Error Words card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L177-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L177-L179

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourcePreparation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instClassicalDecidable

theorem QEC.Distillation.HH18Protocol.physicalErrorWords_card :
    physicalErrorWords.card = Fintype.card PhysicalErrorWord := by sorry
