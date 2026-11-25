-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_deriv
-- name    : ReciprocityTheory.ChartRestriction.DS.toE_deriv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:45.358818+00:00
-- url     : https://prove2.me/theorems/d803c6a1-0374-5b43-8e99-f6073176e32c
-- title:
--   DS: to E deriv
-- statement:
--   The DS construction uses the to E deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L163-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L163-L187

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

theorem ReciprocityTheory.ChartRestriction.DS.toE_deriv {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : EH n) :
    HasDerivAt (fun t : ℝ => toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp ((t : ℂ) • X)) v)
      (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X v) 0 := by sorry
