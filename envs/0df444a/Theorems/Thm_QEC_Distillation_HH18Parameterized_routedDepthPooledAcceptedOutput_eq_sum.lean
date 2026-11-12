-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledAcceptedOutput_eq_sum
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPooledAcceptedOutput_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:06:50.751363+00:00
-- url     : https://prove2.me/theorems/524ce7f2-b261-47f3-8799-fbee7320ecd5
-- title:
--   HH18 Parameterized: routed Depth Pooled Accepted Output eq sum
-- statement:
--   Coercing the pooled expected accepted-output count exposes its literal
--   finite sum of path-survival factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L270-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L270-L279

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPooledAcceptedOutput_eq_sum {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthPooledAcceptedOutput h hdegree epsilon hsmall depth : ℝ) =
      ∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) := by sorry
