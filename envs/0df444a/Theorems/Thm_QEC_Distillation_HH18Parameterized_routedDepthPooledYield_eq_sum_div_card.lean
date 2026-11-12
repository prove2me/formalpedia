-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_eq_sum_div_card
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPooledYield_eq_sum_div_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:39:52.4082+00:00
-- url     : https://prove2.me/theorems/674d37a2-9a70-4690-8958-ece2ba409f56
-- title:
--   HH18 Parameterized: routed Depth Pooled Yield eq sum div card
-- statement:
--   The pooled yield is the literal finite path sum divided by the exact
--   output-slot cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L305-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L305-L316

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPooledYield_eq_sum_div_card {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) =
      (∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ)) /
        Fintype.card (routedDepthOutputSlots m w depth) := by sorry
