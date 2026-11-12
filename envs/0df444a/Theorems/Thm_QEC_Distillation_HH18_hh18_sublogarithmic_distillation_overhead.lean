-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_hh18_sublogarithmic_distillation_overhead
-- name    : QEC.Distillation.HH18.hh18_sublogarithmic_distillation_overhead
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T23:07:24.834196+00:00
-- url     : https://prove2.me/theorems/8d05c467-edc1-486f-b3b8-4d80364eda2f
-- title:
--   HH18: hh18 sublogarithmic distillation overhead
-- statement:
--   The source-exact HH18 family has an exponent arbitrarily close to its
--   interval infimum and below one, while its actual finite-depth protocols have
--   polylogarithmic successful-output cost and vanishing output error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/SublogarithmicOverhead.lean#L128-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/SublogarithmicOverhead.lean#L128-L244

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_SelectedCode
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
import Definitions.Def_QEC_Results_Distillation_SublogarithmicOverhead
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18
open Coding
open Coding.PuncturedReedMuller
open Filter Topology
open Semantics
open Semantics.FiniteInstrument
open QEC.Distillation.HH18PuncturedReedMuller
open HH18SublogarithmicEntropy
open HH18Parameterized

theorem QEC.Distillation.HH18.hh18_sublogarithmic_distillation_overhead (eta : ℝ) (heta : 0 < eta) :
    ∃ q : ℚ, ∃ A D j : Nat,
      (1 / 6 : ℚ) < q ∧ q < (1 / 3 : ℚ) ∧
      0 < A ∧ 0 < D ∧ 3 * A < D ∧ 0 < j ∧ q = (A : ℚ) / D ∧
      let r := parameterR D j
      let w := parameterW A j
      let m := parameterM D j
      let n := parameterLength A D j
      let k := parameterDimension A D j
      let d := parameterDistance A D j
      ∃ h : Admissible w r m,
        m = 3 * r + 1 ∧ 0 ≤ 2 * w ∧ 2 * w < 2 * r ∧ 2 * r < m ∧
        (w : ℚ) = 3 * (r : ℚ) * q ∧
        Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite m w) = n ∧
        Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite m w) - Dimension (xCode w r m) -
            Dimension (zCode w r m) = k ∧
        Module.finrank Complex (cssCode h).stabilizer.code.carrier = 2 ^ k ∧
        StabilizerCode.SemanticStabilizerDistance (sourceValidStabilizer h) d ∧
        (encodedCode h).ImplementsLogicalGate (physicalT w m) (logicalTInv w m) ∧
        (encodedCode h).ImplementsLogicalGate (physicalTInv w m) (logicalT w m) ∧
        hh18GammaInf ≤ hh18Gamma p0R ∧ hh18Gamma p0R < (339 / 500 : ℝ) ∧
        (339 / 500 : ℝ) < 1 ∧
        ∃ epsilon : HH18NoisyInput.DiagonalErrorRate,
          0 < epsilon.1 ∧
          ∃ hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon,
          ∃ gamma : ℝ,
            gamma = routedDepthScheduleGamma w r m ∧
            gamma = Real.log ((n : ℝ) / k) / Real.log d ∧
            |gamma - hh18GammaInf| < eta ∧ gamma < 1 ∧
          ∃ coefficient : ℝ,
            coefficient = decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon ∧
            0 < coefficient ∧ 0 ≤ coefficient ∧
            (∀ depth : Nat,
              PolylogarithmicOverhead
                (decodedRetryPoolPhysicalExactBatchProtocolFamily h
                  (selected_transversal_t_degree A D j) epsilon
                  hpool depth
                  decodedRetryPoolTensorUnitDensity)
                gamma coefficient ∧
              decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost h
                (selected_transversal_t_degree A D j) epsilon depth
                decodedRetryPoolTensorUnitDensity =
                DistillationProtocolFamily.successfulOutputCost
                  (decodedRetryPoolPhysicalExactBatchProtocolFamily h
                  (selected_transversal_t_degree A D j) epsilon
                  hpool depth
                  decodedRetryPoolTensorUnitDensity) PUnit.unit) ∧
            Tendsto (fun depth : Nat =>
              routedDepthScheduleTargetError w r m epsilon (depth + 1)) atTop (𝓝 0) ∧
            Tendsto (fun depth : Nat =>
              decodedRetryPoolPhysicalExactBatchActualOutputError h
                (selected_transversal_t_degree A D j) epsilon depth
                decodedRetryPoolTensorUnitDensity) atTop (𝓝 0) := by sorry
