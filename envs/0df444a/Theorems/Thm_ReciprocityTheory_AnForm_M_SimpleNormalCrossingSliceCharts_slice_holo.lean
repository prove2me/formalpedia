-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_slice_holo
-- name    : ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.slice_holo
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:32.840124+00:00
-- url     : https://prove2.me/theorems/b9ae59b1-279f-4774-93f6-b8f9cea11603
-- title:
--   Simple Normal Crossing Slice Charts: slice holo
-- statement:
--   The Simple Normal Crossing Slice Charts construction uses the slice holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L183-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L183-L203

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

theorem ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.slice_holo {e : ℕ} (A : FinHolAtlas (e + 1) X) (S : Set X)
    {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
    (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w0 : S) (hc : IsCompatChart A ψ) (k : Fin A.n) :
    AnalyticOnNhd ℂ (A.chart k ∘ Subtype.val ∘ (sliceChart ψ i S hS w0).symm)
      ((sliceChart ψ i S hS w0).target ∩
        (sliceChart ψ i S hS w0).symm ⁻¹' (Subtype.val ⁻¹' (A.chart k).source)) := by sorry
