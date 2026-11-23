-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_locDens_piece
-- name    : ReciprocityTheory.AnForm.M.st_locDens_piece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:45.328801+00:00
-- url     : https://prove2.me/theorems/1fa995bc-c928-42ad-bcac-22ecc8fe8e37
-- title:
--   M: st loc Dens piece
-- statement:
--   The M construction uses the st loc Dens piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L149-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L149-L189

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
include hΦ hG hGU

theorem ReciprocityTheory.AnForm.M.st_locDens_piece (u : X → ℝ) (hu : A.Smooth u) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :
    locDens A (Fin.cons (LocPot.ofFun u) Φ) j y =
      maDens (Fin.cons (u ∘ (A.chart j).symm) fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by sorry
