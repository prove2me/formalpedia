-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_intTsum
-- name    : ReciprocityTheory.AnForm.M.pushA_intTsum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:32.918598+00:00
-- url     : https://prove2.me/theorems/d96670f1-8b01-4df2-930d-458ef7e5b33d
-- title:
--   M: push A int Tsum
-- statement:
--   The M construction uses the push A int Tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L219-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L219-L233

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.pushA_intTsum {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hsum : ∀ a, Summable fun i => F i a)
    (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) : Integrable (fun a => ∑' i, F i a) μ := by sorry
