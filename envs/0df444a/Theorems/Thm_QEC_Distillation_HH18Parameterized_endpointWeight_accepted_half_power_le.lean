-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_half_power_le
-- name    : QEC.Distillation.HH18Parameterized.endpointWeight_accepted_half_power_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:01:09.968915+00:00
-- url     : https://prove2.me/theorems/83bbdd44-eca3-496f-a0bd-be9d3fbff465
-- title:
--   HH18 Parameterized: endpoint Weight accepted half power le
-- statement:
--   The actual accepted endpoint retains the uniform lower bound inherited
--   from its all-zero physical resource-error branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L100-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L100-L106

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.endpointWeight_accepted_half_power_le {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 / 2 : ℝ) ^ physicalInputCount m w ≤
      endpointWeight h hdegree (noisyResources m w epsilon) .accepted := by sorry
