-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rotateTInvResource_error
-- name    : QEC.Distillation.HH18Protocol.rotateTInvResource_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:55:34.996368+00:00
-- url     : https://prove2.me/theorems/dd4faabe-a50f-4229-970a-108dbdc08330
-- title:
--   HH18 Protocol: rotate TInv Resource error
-- statement:
--   The physical `S` rotation sends the selected diagonal `Z` error to the
--   negative A-basis eigenstate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L96-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourcePreparation.lean#L96-L112

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

theorem QEC.Distillation.HH18Protocol.rotateTInvResource_error :
    rotateTInvResource (HH18NoisyInput.tInvResourceErrorDensity 1) =
      Triorthogonal.BH12NoisyInjection.OneQubit.aOneDensity := by sorry
