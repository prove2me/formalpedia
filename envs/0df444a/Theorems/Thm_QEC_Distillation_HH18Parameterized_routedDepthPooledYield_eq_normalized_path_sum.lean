-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_eq_normalized_path_sum
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPooledYield_eq_normalized_path_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:50:36.70844+00:00
-- url     : https://prove2.me/theorems/e3d159bd-8d72-4fd8-aabf-87e5b5b24739
-- title:
--   HH18 Parameterized: routed Depth Pooled Yield eq normalized path sum
-- statement:
--   The pooled yield normalizes the literal finite path sum by the exact
--   `k^z` routed output-slot cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L320-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L320-L331

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPooledYield_eq_normalized_path_sum {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) =
      (∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ)) /
        (logicalOutputCount m w : ℝ) ^ depth := by sorry
