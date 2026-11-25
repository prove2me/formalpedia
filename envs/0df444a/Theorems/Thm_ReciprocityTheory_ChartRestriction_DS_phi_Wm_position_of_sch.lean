-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_Wm_position_of_sch
-- name    : ReciprocityTheory.ChartRestriction.DS.phi_Wm_position_of_sch
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:27.528331+00:00
-- url     : https://prove2.me/theorems/c414912d-dcef-5453-a2d7-901abceb1560
-- title:
--   DS: phi Wm position of sch
-- statement:
--   The DS construction uses the phi Wm position of sch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchForm.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchForm.lean#L31-L48

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

theorem ReciprocityTheory.ChartRestriction.DS.phi_Wm_position_of_sch (hE : IsGlRep E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M}
    (hF0 : F ∈ ncV ε V (k + 1)) (hF : ∀ κ, slice i κ F ∈ Wm ε E V) :
    phi E (k + 1) F ∈ layer ε E V k := by sorry
