-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_exists_sheet_partition
-- name    : ReciprocityTheory.AnForm.M.exists_sheet_partition
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:49.941814+00:00
-- url     : https://prove2.me/theorems/2a43dc74-07b6-4d07-9ce7-903351bbecf9
-- title:
--   M: exists sheet partition
-- statement:
--   The M construction uses the exists sheet partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeInt.lean#L60-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeInt.lean#L60-L109

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
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
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem ReciprocityTheory.AnForm.M.exists_sheet_partition [CompactSpace Y] [T2Space Y] [CompactSpace X] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) [MeasurableSpace X] [BorelSpace X] [Nonempty X] :
    ∃ (E V : ℕ → Set X) (k : ℕ → Fin A.n) (W : ℕ → Fin d → Set Y) (j : ℕ → Fin d → Fin B.n),
      (∀ m, MeasurableSet (E m)) ∧ Pairwise (Function.onFun Disjoint E) ∧
      (⋃ m, E m) = Sᶜ ∧ (∀ m, E m ⊆ V m) ∧
      ∀ m, IsOpen (V m) ∧ V m ⊆ (A.chart (k m)).source ∧ (∀ i, IsOpen (W m i)) ∧
        Pairwise (Function.onFun Disjoint (W m)) ∧ h ⁻¹' V m = ⋃ i, W m i ∧
        ∀ i, Set.BijOn h (W m i) (V m) ∧ W m i ⊆ (B.chart (j m i)).source := by sorry
