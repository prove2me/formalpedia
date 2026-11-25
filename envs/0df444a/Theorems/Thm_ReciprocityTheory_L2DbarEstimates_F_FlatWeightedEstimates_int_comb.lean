-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_int_comb
-- name    : ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.int_comb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:56:21.760369+00:00
-- url     : https://prove2.me/theorems/3f15f0c8-8078-5db9-9ffe-64e96bd10b7e
-- title:
--   Flat Weighted Estimates: int comb
-- statement:
--   The Flat Weighted Estimates construction uses the int comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L40-L52

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates

theorem ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.int_comb {n : ℕ} {f : V n → ℂ} (hf : LocallyIntegrable f volume) {φ : V n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (a b : ℂ) (u w : V n) :
    Integrable (fun y => f y * (a * fderiv ℝ φ y u + b * fderiv ℝ φ y w)) volume ∧
    ∫ y, f y * (a * fderiv ℝ φ y u + b * fderiv ℝ φ y w) =
      a * (∫ y, f y * fderiv ℝ φ y u) + b * ∫ y, f y * fderiv ℝ φ y w := by sorry
