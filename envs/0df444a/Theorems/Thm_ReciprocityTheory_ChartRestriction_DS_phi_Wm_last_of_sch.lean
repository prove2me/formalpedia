-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_Wm_last_of_sch
-- name    : ReciprocityTheory.ChartRestriction.DS.phi_Wm_last_of_sch
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:51.238718+00:00
-- url     : https://prove2.me/theorems/c7064b07-4824-4ad7-8011-c121c3c426a5
-- title:
--   DS: phi Wm last of sch
-- statement:
--   The DS construction uses the phi Wm last of sch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchForm.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchForm.lean#L16-L29

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

theorem ReciprocityTheory.ChartRestriction.DS.phi_Wm_last_of_sch (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by sorry
