-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rotateTInvResource_clean
-- name    : QEC.Distillation.HH18Parameterized.rotateTInvResource_clean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:47:34.116478+00:00
-- url     : https://prove2.me/theorems/5dd1a718-9225-46f9-91d6-9c6ca57d21bd
-- title:
--   HH18 Parameterized: rotate TInv Resource clean
-- statement:
--   The physical rotation sends a clean inverse-T resource to the positive
--   A-basis eigenstate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L42-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L42-L54

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
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
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.rotateTInvResource_clean :
    rotateTInvResource (HH18NoisyInput.tInvResourceErrorDensity 0) =
      Triorthogonal.BH12NoisyInjection.OneQubit.aZeroDensity := by sorry
