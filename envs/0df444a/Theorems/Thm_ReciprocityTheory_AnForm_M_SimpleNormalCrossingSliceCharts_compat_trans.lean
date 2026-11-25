-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_compat_trans
-- name    : ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:30.478634+00:00
-- url     : https://prove2.me/theorems/b8186b47-5d3c-4b68-a4c2-0f58995cbe0e
-- title:
--   Simple Normal Crossing Slice Charts: compat trans
-- statement:
--   The Simple Normal Crossing Slice Charts construction uses the compat trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L141-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L141-L157

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

theorem ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans {e : ℕ} (A : FinHolAtlas e X) {ψ₁ ψ₂ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (h₁ : IsCompatChart A ψ₁) (h₂ : IsCompatChart A ψ₂) {v : Fin e → ℂ} (hv : v ∈ ψ₁.target)
    (hv2 : ψ₁.symm v ∈ ψ₂.source) : AnalyticAt ℂ (ψ₂ ∘ ψ₁.symm) v := by sorry
