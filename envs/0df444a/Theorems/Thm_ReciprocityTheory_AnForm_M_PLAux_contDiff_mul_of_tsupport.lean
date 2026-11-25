-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiff_mul_of_tsupport
-- name    : ReciprocityTheory.AnForm.M.PLAux.contDiff_mul_of_tsupport
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:08.044399+00:00
-- url     : https://prove2.me/theorems/d9f86122-fbb8-5e76-a5ee-d3ffe6afa457
-- title:
--   PLAux: cont Diff mul of tsupport
-- statement:
--   The PLAux construction uses the cont Diff mul of tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean#L121-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean#L121-L132

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffMulOfTsupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff Manifold
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
omit [T2Space X] [CompactSpace X]

theorem ReciprocityTheory.AnForm.M.PLAux.contDiff_mul_of_tsupport {n : ℕ} {ρ f : (Fin n → ℂ) → ℝ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun y => ρ y * f y) := by sorry
