-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_tent_of_abs_le
-- name    : ReciprocityTheory.Cheb.tent_of_abs_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:53.06848+00:00
-- url     : https://prove2.me/theorems/acd1796f-6b1d-4ecf-ae15-d2316d3686f0
-- title:
--   Cheb: tent of abs le
-- statement:
--   The Cheb construction uses the tent of abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L14-L15

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

theorem ReciprocityTheory.Cheb.tent_of_abs_le {t : ℝ} (h : |t| ≤ 1) : tent t = 1 - |t| := by sorry
