-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rotateTInvResource_noisy
-- name    : QEC.Distillation.HH18Parameterized.rotateTInvResource_noisy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:44:52.760331+00:00
-- url     : https://prove2.me/theorems/cfe117aa-85c3-4d3d-a7fb-b3c2d740ca8f
-- title:
--   HH18 Parameterized: rotate TInv Resource noisy
-- statement:
--   Rotating the actual noisy inverse-T resource yields the existing A-basis
--   diagonal mixture with the same physical error rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L87-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L87-L111

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

theorem QEC.Distillation.HH18Parameterized.rotateTInvResource_noisy
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rotateTInvResource (HH18NoisyInput.noisyTInvResource epsilon) =
      Triorthogonal.BH12NoisyInjection.OneQubit.diagonalAResource
        (aBasisErrorParameter epsilon) := by sorry
