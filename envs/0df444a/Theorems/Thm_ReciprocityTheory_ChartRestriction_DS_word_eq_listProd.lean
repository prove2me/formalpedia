-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_word_eq_listProd
-- name    : ReciprocityTheory.ChartRestriction.DS.word_eq_listProd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:44.183794+00:00
-- url     : https://prove2.me/theorems/5edf0493-325f-4f97-afe7-8683e2fc8ce9
-- title:
--   DS: word eq list Prod
-- statement:
--   The DS construction uses the word eq list Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L99-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.word_eq_listProd {k : ℕ} (κ : Fin k → Fin n × Fin n) :
    word E κ = ((List.ofFn κ).map fun p => E p.1 p.2).prod := by sorry
