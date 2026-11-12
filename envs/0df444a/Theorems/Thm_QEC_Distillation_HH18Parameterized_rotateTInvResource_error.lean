-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rotateTInvResource_error
-- name    : QEC.Distillation.HH18Parameterized.rotateTInvResource_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:47:33.686273+00:00
-- url     : https://prove2.me/theorems/77c05898-926b-4d41-9342-c4f8d42bffcc
-- title:
--   HH18 Parameterized: rotate TInv Resource error
-- statement:
--   The same physical rotation sends a diagonal-Z-error inverse-T resource to
--   the negative A-basis eigenstate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L58-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L58-L75

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

theorem QEC.Distillation.HH18Parameterized.rotateTInvResource_error :
    rotateTInvResource (HH18NoisyInput.tInvResourceErrorDensity 1) =
      Triorthogonal.BH12NoisyInjection.OneQubit.aOneDensity := by sorry
