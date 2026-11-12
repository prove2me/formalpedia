-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_resourceConsumerBranch_basis
-- name    : QEC.Distillation.HH18Protocol.resourceConsumerBranch_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:03:06.652974+00:00
-- url     : https://prove2.me/theorems/63b2308d-d616-48ea-928c-f54fb63adabb
-- title:
--   HH18 Protocol: resource Consumer Branch basis
-- statement:
--   The HH18 Protocol construction uses the resource Consumer Branch basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceKraus.lean#L78-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceKraus.lean#L78-L88

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourcePreparation
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceKraus
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
attribute [local instance] QEC.Distillation.HH18Protocol.instKrausClassicalDecidable

theorem QEC.Distillation.HH18Protocol.resourceConsumerBranch_basis
    (error observed : PhysicalErrorWord) :
    resourceConsumerKrausFamily.operator error (errorWordBasisState observed) =
      if error = observed then errorBranchState error else 0 := by sorry
