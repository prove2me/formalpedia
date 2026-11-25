-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_left_piece
-- name    : ReciprocityTheory.AnForm.M.st_left_piece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:58:30.95389+00:00
-- url     : https://prove2.me/theorems/a5d951fb-5bcb-45b6-9c15-276f5a661852
-- title:
--   M: st left piece
-- statement:
--   The M construction uses the st left piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L193-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L193-L219

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
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
include hΦ hGo hG hGU

theorem ReciprocityTheory.AnForm.M.st_left_piece (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun w) Φ) ψ =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) y *
          maDens (Fin.cons (w ∘ (A.chart j).symm)
            fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by sorry
