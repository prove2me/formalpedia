-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_resourceConsumerChannel_errorWordBasisDensity
-- name    : QEC.Distillation.HH18Protocol.resourceConsumerChannel_errorWordBasisDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:06:00.98584+00:00
-- url     : https://prove2.me/theorems/53bbec90-303e-4e2e-8e61-818918973523
-- title:
--   HH18 Protocol: resource Consumer Channel error Word Basis Density
-- statement:
--   The narrow public inter-module bridge for the exact per-basis channel action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceDiagonal.lean#L92-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceDiagonal.lean#L92-L110

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceKraus
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceDiagonal
import Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchState_normSq

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instDiagonalClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instDiagonalClassicalDecidable

theorem QEC.Distillation.HH18Protocol.resourceConsumerChannel_errorWordBasisDensity
    (observed : PhysicalErrorWord) :
    resourceConsumerChannel (errorWordBasisDensity observed).toOperator =
      (DensityOperator.pureDensity (errorBranchState observed)
        (errorBranchState_normSq observed)).toOperator := by sorry
