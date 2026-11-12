-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rotateTInvResource_noisy
-- name    : QEC.Distillation.HH18Protocol.rotateTInvResource_noisy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:51:42.25521+00:00
-- url     : https://prove2.me/theorems/64a67775-f52c-4fa6-947b-9513a7e97ce1
-- title:
--   HH18 Protocol: rotate TInv Resource noisy
-- statement:
--   After the physical `S` rotation, the actual HH18 diagonal `T†` resource
--   is exactly the A-basis diagonal mixture with the same error rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L124-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L124-L150

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

theorem QEC.Distillation.HH18Protocol.rotateTInvResource_noisy
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rotateTInvResource (HH18NoisyInput.noisyTInvResource epsilon) =
      Triorthogonal.BH12NoisyInjection.OneQubit.diagonalAResource
        (aBasisErrorParameter epsilon) := by sorry
