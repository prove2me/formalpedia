-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.rsM_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:35.056936+00:00
-- url     : https://prove2.me/theorems/bfc0cccd-e210-559d-b831-482cf7ace783
-- title:
--   DS: rs M apply
-- statement:
--   The DS construction uses the rs M apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L35-L36

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

theorem ReciprocityTheory.ChartRestriction.DS.rsM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : (⊤ : Submodule ℂ (EH n))) :
    ((rsM A v : (⊤ : Submodule ℂ (EH n))) : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A v := by sorry
