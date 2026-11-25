-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_tent_sub_tent_le__c56d69
-- name    : ReciprocityTheory.Cheb.abs_tent_sub_tent_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:56.583004+00:00
-- url     : https://prove2.me/theorems/c56d6919-c776-475c-b337-94f5f71140d4
-- title:
--   Cheb: abs tent sub tent le
-- statement:
--   The Cheb construction uses the abs tent sub tent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L20-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.abs_tent_sub_tent_le (s t : ℝ) : |tent s - tent t| ≤ |s - t| := by sorry
