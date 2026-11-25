-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_dbarAt_eq_zero_of_holo
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.dbarAt_eq_zero_of_holo
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:02:32.735198+00:00
-- url     : https://prove2.me/theorems/828ddbf1-9d11-5fb6-a73a-d963daa98302
-- title:
--   Weighted Atlas: dbar At eq zero of holo
-- statement:
--   The Weighted Atlas construction uses the dbar At eq zero of holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxF.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxF.lean#L20-L23

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.dbarAt_eq_zero_of_holo (j : ι) (F : ι → Y → ℂ) (y : Y) {G : V n → ℂ}
    (hF : (F j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] G) (hG : DifferentiableAt ℂ G (A.chart j y))
    (ξ : Fin n → ℂ) : A.dbarAt j F y ξ = 0 := by sorry
