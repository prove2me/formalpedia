-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rotateTInvResource_clean
-- name    : QEC.Distillation.HH18Protocol.rotateTInvResource_clean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:55:52.216091+00:00
-- url     : https://prove2.me/theorems/63f90421-9759-46f4-bee2-52a431eee563
-- title:
--   HH18 Protocol: rotate TInv Resource clean
-- statement:
--   The physical `S` rotation sends the clean `T†` resource to the positive
--   eigenstate of the measured A basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L80-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L80-L92

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

theorem QEC.Distillation.HH18Protocol.rotateTInvResource_clean :
    rotateTInvResource (HH18NoisyInput.tInvResourceErrorDensity 0) =
      Triorthogonal.BH12NoisyInjection.OneQubit.aZeroDensity := by sorry
