-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_isClosed_divisorComponent
-- name    : ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.isClosed_divisorComponent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:52.012458+00:00
-- url     : https://prove2.me/theorems/8aa64476-deb0-4ff3-b4f7-2ea51230d938
-- title:
--   Simple Normal Crossing Slice Charts: is Closed divisor Component
-- statement:
--   The Simple Normal Crossing Slice Charts construction uses the is Closed divisor Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L14-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L14-L44

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
variable {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.isClosed_divisorComponent {e : ℕ} (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (W : Fin r → Set X) (h : IsSNC A L s m W) (k : Fin r) : IsClosed (W k) := by sorry
