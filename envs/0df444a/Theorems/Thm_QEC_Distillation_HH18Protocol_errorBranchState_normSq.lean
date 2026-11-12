-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchState_normSq
-- name    : QEC.Distillation.HH18Protocol.errorBranchState_normSq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:51:33.049544+00:00
-- url     : https://prove2.me/theorems/c5a55666-9f65-446b-bfd9-56823c50ab4f
-- title:
--   HH18 Protocol: error Branch State norm Sq
-- statement:
--   The HH18 Protocol construction uses the error Branch State norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L269-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L269-L289

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

theorem QEC.Distillation.HH18Protocol.errorBranchState_normSq (error : PhysicalErrorWord) :
    ‖errorBranchState error‖ ^ 2 = 1 := by sorry
