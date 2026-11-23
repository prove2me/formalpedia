-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_gap_at_noncompact_weight
-- name    : ReciprocityTheory.ChartRestriction.DS.casimir_gap_at_noncompact_weight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:49.306281+00:00
-- url     : https://prove2.me/theorems/3abf3d54-c991-4a3b-b6be-d2cb587489ec
-- title:
--   DS: casimir gap at noncompact weight
-- statement:
--   The DS construction uses the casimir gap at noncompact weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasimirGapAtNoncompactWeight.lean#L39-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasimirGapAtNoncompactWeight.lean#L39-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.casimir_gap_at_noncompact_weight (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ genSub E V) (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) (hne : μ ≠ lowK ε lam) :
    ∃ j : ℕ, IsNCSum ε (j + 1) (μ - lowK ε lam) ∧ 0 < h - n + 1 ∧
      casValK ε (lowK ε lam) + 2 * ((j : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ := by sorry
