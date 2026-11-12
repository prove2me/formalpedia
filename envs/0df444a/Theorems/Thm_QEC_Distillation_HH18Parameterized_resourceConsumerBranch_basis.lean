-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_resourceConsumerBranch_basis
-- name    : QEC.Distillation.HH18Parameterized.resourceConsumerBranch_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:58:10.251694+00:00
-- url     : https://prove2.me/theorems/21a3d4fa-7f53-48b2-ac13-d0379a613a56
-- title:
--   HH18 Parameterized: resource Consumer Branch basis
-- statement:
--   The HH18 Parameterized construction uses the resource Consumer Branch basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumer.lean#L93-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumer.lean#L93-L105

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumerSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instConsumerClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instConsumerClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.resourceConsumerBranch_basis {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error observed : PhysicalErrorWord m w) :
    (resourceConsumerKrausFamily h hdegree).operator error
      (errorWordBasisState m w observed) =
      if error = observed then errorBranchState h hdegree error else 0 := by sorry
