-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_update_eq_slRest
-- name    : ReciprocityTheory.ChartRestriction.DS.update_eq_slRest
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:53.194819+00:00
-- url     : https://prove2.me/theorems/d4fc7196-1338-4dbf-9728-24a9d1ea108d
-- title:
--   DS: update eq sl Rest
-- statement:
--   The DS construction uses the update eq sl Rest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L35-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
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
  {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.update_eq_slRest {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (q : Fin n × Fin n) :
    Function.update κ i q = (slRest i).symm (q, (slRest i κ).2) := by sorry
