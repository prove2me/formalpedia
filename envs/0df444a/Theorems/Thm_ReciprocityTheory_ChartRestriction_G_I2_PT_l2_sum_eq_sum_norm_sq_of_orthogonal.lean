-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_l2_sum_eq_sum_norm_sq_of_orthogonal
-- name    : ReciprocityTheory.ChartRestriction.G.I2.PT.l2_sum_eq_sum_norm_sq_of_orthogonal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:02.235888+00:00
-- url     : https://prove2.me/theorems/640745e5-a303-5edd-8661-7b83e754309d
-- title:
--   PT: l2 sum eq sum norm sq of orthogonal
-- statement:
--   The PT construction uses the l2 sum eq sum norm sq of orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L73-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L73-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.PT.l2_sum_eq_sum_norm_sq_of_orthogonal {n : ℕ} (q : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (e : ι → (Fin n → Vsp X.dim) → ℂ) (he : ∀ i ∈ s, Continuous (e i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → X.l2ip q (e i) (e j) = 0) :
    X.l2 q (fun v => ∑ i ∈ s, c i * e i v) = ∑ i ∈ s, ‖c i‖ ^ 2 * X.l2 q (e i) := by sorry
