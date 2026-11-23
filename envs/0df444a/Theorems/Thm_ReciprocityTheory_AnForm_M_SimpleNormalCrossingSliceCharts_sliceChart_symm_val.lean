-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_sliceChart_symm_val
-- name    : ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.sliceChart_symm_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:14.730741+00:00
-- url     : https://prove2.me/theorems/2a39163c-0ee0-4ba9-b83e-6712cdd5ee2c
-- title:
--   Simple Normal Crossing Slice Charts: slice Chart symm val
-- statement:
--   The Simple Normal Crossing Slice Charts construction uses the slice Chart symm val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L102-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L102-L120

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
open Classical

theorem ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.sliceChart_symm_val {e : ℕ} (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ))
    (i : Fin (e + 1)) (S : Set X) (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w0 : S)
    {z : Fin e → ℂ} (hz : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target) :
    ((sliceChart ψ i S hS w0).symm z : X) = ψ.symm (Fin.insertNth (α := fun _ => ℂ) i 0 z) := by sorry
