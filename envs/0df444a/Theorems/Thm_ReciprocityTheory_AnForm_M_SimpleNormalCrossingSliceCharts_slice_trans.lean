-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_slice_trans
-- name    : ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.slice_trans
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:03.694326+00:00
-- url     : https://prove2.me/theorems/452a0951-d841-5cb9-a719-6d45e29f2498
-- title:
--   Simple Normal Crossing Slice Charts: slice trans
-- statement:
--   The Simple Normal Crossing Slice Charts construction uses the slice trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L159-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L159-L181

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

theorem ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.slice_trans {e : ℕ} (A : FinHolAtlas (e + 1) X) (S : Set X)
    {ψ₁ ψ₂ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i₁ i₂ : Fin (e + 1)}
    (h₁ : ∀ y ∈ ψ₁.source, y ∈ S ↔ ψ₁ y i₁ = 0) (h₂ : ∀ y ∈ ψ₂.source, y ∈ S ↔ ψ₂ y i₂ = 0)
    (w₁ w₂ : S) (hc₁ : IsCompatChart A ψ₁) (hc₂ : IsCompatChart A ψ₂) :
    AnalyticOnNhd ℂ (sliceChart ψ₂ i₂ S h₂ w₂ ∘ (sliceChart ψ₁ i₁ S h₁ w₁).symm)
      ((sliceChart ψ₁ i₁ S h₁ w₁).target ∩
        (sliceChart ψ₁ i₁ S h₁ w₁).symm ⁻¹' (sliceChart ψ₂ i₂ S h₂ w₂).source) := by sorry
