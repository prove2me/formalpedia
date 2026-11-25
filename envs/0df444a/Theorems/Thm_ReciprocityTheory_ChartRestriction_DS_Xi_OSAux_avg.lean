-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_avg
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.avg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:52.769397+00:00
-- url     : https://prove2.me/theorems/a331e4d9-c487-5f5f-ba41-fb09a6389f32
-- title:
--   OSAux: avg
-- statement:
--   The OSAux construction uses the avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentConditionNeg.lean#L12-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentConditionNeg.lean#L12-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LintegralInsertFiberLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DeZeroBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentConditionNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.avg {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ] (Φ : ℝ → X → X)
    (hΦm : Measurable (fun q : ℝ × X => Φ q.1 q.2))
    (hΦ : ∀ t ∈ Icc (1 : ℝ) 2, MeasurePreserving (Φ t) μ μ) {f w : X → ℝ≥0∞}
    (hf : Measurable f) (hw : Measurable w) (K : ℝ≥0∞)
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, ∀ x, f (Φ t x) ≤ K * f x) :
    ∫⁻ x, f x * w x ∂μ ≤ K * ∫⁻ x, f x * (∫⁻ t in Icc (1 : ℝ) 2, w (Φ t x)) ∂μ := by sorry
