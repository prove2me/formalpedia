-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthTypedSuccessfulOutputCost_eq
-- name    : QEC.Distillation.HH18Parameterized.routedDepthTypedSuccessfulOutputCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:38:21.969571+00:00
-- url     : https://prove2.me/theorems/b6ba42ef-dc8b-4979-9a35-844c49025a04
-- title:
--   HH18 Parameterized: routed Depth Typed Successful Output Cost eq
-- statement:
--   The typed successful-output cost has its exact finite routed
--   input/output ratio and pooled-yield form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L379-L392
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L379-L392

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthTypedSuccessfulOutputCost_eq {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall depth =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth /
        (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) := by sorry
