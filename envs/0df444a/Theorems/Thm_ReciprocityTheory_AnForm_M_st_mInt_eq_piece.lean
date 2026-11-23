-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_eq_piece
-- name    : ReciprocityTheory.AnForm.M.st_mInt_eq_piece
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:59.888635+00:00
-- url     : https://prove2.me/theorems/51b6f2b8-04d9-4728-81f9-dac41d436289
-- title:
--   M: st m Int eq piece
-- statement:
--   The M construction uses the st m Int eq piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L128-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L128-L139

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
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

theorem ReciprocityTheory.AnForm.M.st_mInt_eq_piece [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (j : Fin A.n) (G : Set X)
    (hG : G ⊆ (A.chart j).source) (g : X → ℝ) (hg : Continuous g) (hgs : tsupport g ⊆ G) :
    mInt A Ψ g = ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
      g ((A.chart j).symm y) * locDens A Ψ j y := by sorry
