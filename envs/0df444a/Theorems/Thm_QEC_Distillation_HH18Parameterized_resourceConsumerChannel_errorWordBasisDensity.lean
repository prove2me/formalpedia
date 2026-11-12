-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_resourceConsumerChannel_errorWordBasisDensity
-- name    : QEC.Distillation.HH18Parameterized.resourceConsumerChannel_errorWordBasisDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:58:16.04436+00:00
-- url     : https://prove2.me/theorems/26f64c00-1ac9-42fe-bf44-415918d10af4
-- title:
--   HH18 Parameterized: resource Consumer Channel error Word Basis Density
-- statement:
--   The word consumer maps each basis-word density to the corresponding
--   normalized actual error branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumer.lean#L178-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumer.lean#L178-L198

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumerSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranchState_normSq

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

theorem QEC.Distillation.HH18Parameterized.resourceConsumerChannel_errorWordBasisDensity {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (observed : PhysicalErrorWord m w) :
    resourceConsumerChannel h hdegree
      (errorWordBasisDensity m w observed).toOperator =
      (DensityOperator.pureDensity (errorBranchState h hdegree observed)
        (errorBranchState_normSq h hdegree observed)).toOperator := by sorry
