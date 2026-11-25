-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_partsHyp_piece
-- name    : ReciprocityTheory.AnForm.M.st_partsHyp_piece
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:10.917883+00:00
-- url     : https://prove2.me/theorems/c1da085a-d89f-4592-834c-0e482b3c9047
-- title:
--   M: st parts Hyp piece
-- statement:
--   The M construction uses the st parts Hyp piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L88-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L88-L123

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
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
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
include hΦ hGo hG hGU

theorem ReciprocityTheory.AnForm.M.st_partsHyp_piece (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ)
    (hψG : tsupport ψ ⊆ G) :
    PartsHyp (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
      ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by sorry
