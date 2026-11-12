-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_noisyResources_permitted
-- name    : QEC.Distillation.HH18Protocol.noisyResources_permitted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:55:12.508349+00:00
-- url     : https://prove2.me/theorems/14f62bc6-3c24-4d08-a093-96f7219b71a4
-- title:
--   HH18 Protocol: noisy Resources permitted
-- statement:
--   The HH18 Protocol construction uses the noisy Resources permitted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L58-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L58-L65

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

theorem QEC.Distillation.HH18Protocol.noisyResources_permitted
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    InputErrorModel.Permits (.independent (independentInputModel epsilon))
      (noisyResources epsilon) := by sorry
