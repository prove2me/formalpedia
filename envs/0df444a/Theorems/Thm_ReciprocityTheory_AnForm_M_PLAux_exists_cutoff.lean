-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_exists_cutoff
-- name    : ReciprocityTheory.AnForm.M.PLAux.exists_cutoff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:42.705372+00:00
-- url     : https://prove2.me/theorems/1a31bb79-89de-5994-99b9-4bfe08c75a78
-- title:
--   PLAux: exists cutoff
-- statement:
--   The PLAux construction uses the exists cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean#L74-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean#L74-L119

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

theorem ReciprocityTheory.AnForm.M.PLAux.exists_cutoff {n : ℕ} {K U : Set (Fin n → ℂ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ ρ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ ρ ∧ IsCompact (tsupport ρ) ∧ tsupport ρ ⊆ U ∧
      ∃ O, IsOpen O ∧ K ⊆ O ∧ ∀ y ∈ O, ρ y = 1 := by sorry
