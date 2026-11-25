-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_nonpos_piece
-- name    : ReciprocityTheory.AnForm.M.st_nonpos_piece
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:00.856107+00:00
-- url     : https://prove2.me/theorems/ed55c583-65bf-5016-816a-ebd6c4b17305
-- title:
--   M: st nonpos piece
-- statement:
--   The M construction uses the st nonpos piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L127-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L127-L210

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

theorem ReciprocityTheory.AnForm.M.st_nonpos_piece (hP : PartsStatement) (v θ : X → ℝ) (hv : A.Smooth v)
    (hθ : A.Smooth θ) (hθG : tsupport θ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ x * v x) =
      -(∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
          (A.chart j).target.indicator (θ ∘ (A.chart j).symm) y *
            gradDens (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) (v ∘ (A.chart j).symm)
              (v ∘ (A.chart j).symm) y) +
        mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) θ := by sorry
