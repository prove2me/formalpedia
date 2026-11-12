-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthFiniteOneSubSum_le_product
-- name    : QEC.Distillation.HH18Parameterized.routedDepthFiniteOneSubSum_le_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:06:19.612647+00:00
-- url     : https://prove2.me/theorems/a0ef358a-9973-4f28-8e63-3c6945cf6618
-- title:
--   HH18 Parameterized: routed Depth Finite One Sub Sum le product
-- statement:
--   A finite product of factors in the unit interval is bounded below by one
--   minus the sum of their losses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L131-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L131-L153

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

theorem QEC.Distillation.HH18Parameterized.routedDepthFiniteOneSubSum_le_product {ι : Type*} (s : Finset ι)
    (loss : ι → ℝ) (hlossNonneg : ∀ item ∈ s, 0 ≤ loss item)
    (hlossLeOne : ∀ item ∈ s, loss item ≤ 1) :
    1 - ∑ item ∈ s, loss item ≤ ∏ item ∈ s, (1 - loss item) := by sorry
