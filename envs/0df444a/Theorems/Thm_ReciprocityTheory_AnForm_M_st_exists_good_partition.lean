-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_exists_good_partition
-- name    : ReciprocityTheory.AnForm.M.st_exists_good_partition
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:52.73658+00:00
-- url     : https://prove2.me/theorems/15669735-20b8-47ee-93cc-e4057e59d0ab
-- title:
--   M: st exists good partition
-- statement:
--   The M construction uses the st exists good partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesB.lean#L17-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesB.lean#L17-L73

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.st_exists_good_partition [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) {r : ℕ}
    (Φ : Fin r → LocPot X) :
    ∃ (M : ℕ) (θ : Fin M → X → ℝ) (G : Fin M → Set X) (j : Fin M → Fin A.n)
      (x0 : Fin M → Fin r → X),
      (∀ m, A.Smooth (θ m)) ∧ (∀ m x, 0 ≤ θ m x) ∧ (∀ x, ∑ m, θ m x = 1) ∧
      (∀ m, tsupport (θ m) ⊆ G m) ∧ (∀ m, IsOpen (G m)) ∧
      (∀ m, G m ⊆ (A.chart (j m)).source) ∧ (∀ m i, G m ⊆ (Φ i).U (x0 m i)) := by sorry
