-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_exp
-- name    : ReciprocityTheory.ChartRestriction.DS.toE_exp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:20.686588+00:00
-- url     : https://prove2.me/theorems/105d5f43-e648-440b-b9e4-d73639181abb
-- title:
--   DS: to E exp
-- statement:
--   The DS construction uses the to E exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L154-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L154-L161

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.toE_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp X) =
      NormedSpace.exp (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) := by sorry
