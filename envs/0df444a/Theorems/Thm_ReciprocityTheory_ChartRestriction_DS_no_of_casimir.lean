-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_no_of_casimir
-- name    : ReciprocityTheory.ChartRestriction.DS.no_of_casimir
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:42.924456+00:00
-- url     : https://prove2.me/theorems/d832ee2b-8a32-55c0-9bf2-53f83b5e32b8
-- title:
--   DS: no of casimir
-- statement:
--   The DS construction uses the no of casimir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchForm.lean#L273-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SchForm.lean#L273-L344

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

theorem ReciprocityTheory.ChartRestriction.DS.no_of_casimir (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hgap : StdGap ε lam) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by sorry
