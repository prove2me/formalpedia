-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_khw_of_not_sch
-- name    : ReciprocityTheory.ChartRestriction.DS.exists_khw_of_not_sch
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:34.671351+00:00
-- url     : https://prove2.me/theorems/71c0e777-2864-5e86-b5d6-fe8131fb8e4e
-- title:
--   DS: exists khw of not sch
-- statement:
--   The DS construction uses the exists khw of not sch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchForm.lean#L177-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchForm.lean#L177-L209

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.exists_khw_of_not_sch (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hne : ∃ x ∈ Wm ε E V, phi E 1 x ≠ 0) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧
      ∃ w ∈ layer ε E V 1, w ≠ 0 ∧ IsKHWVec ε E (lowK ε lam - root a b) w := by sorry
