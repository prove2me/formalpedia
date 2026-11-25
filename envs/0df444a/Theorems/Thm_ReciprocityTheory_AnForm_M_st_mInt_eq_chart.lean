-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_eq_chart
-- name    : ReciprocityTheory.AnForm.M.st_mInt_eq_chart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:21.333206+00:00
-- url     : https://prove2.me/theorems/472135d1-7113-539c-8194-13df0c2e02bd
-- title:
--   M: st m Int eq chart
-- statement:
--   The M construction uses the st m Int eq chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L120-L126

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

theorem ReciprocityTheory.AnForm.M.st_mInt_eq_chart [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (j : Fin A.n) (g : X → ℝ)
    (hg : Continuous g) (hgs : tsupport g ⊆ (A.chart j).source) :
    mInt A Ψ g = ∫ y in (A.chart j).target, g ((A.chart j).symm y) * locDens A Ψ j y := by sorry
