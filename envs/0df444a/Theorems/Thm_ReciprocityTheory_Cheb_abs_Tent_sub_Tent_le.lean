-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_Tent_sub_Tent_le
-- name    : ReciprocityTheory.Cheb.abs_Tent_sub_Tent_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:11.416841+00:00
-- url     : https://prove2.me/theorems/7ce36fd6-2d6a-5618-a3ac-c00c7e94d6cf
-- title:
--   Cheb: abs Tent sub Tent le
-- statement:
--   The Cheb construction uses the abs Tent sub Tent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L94-L99

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
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.Cheb.abs_Tent_sub_Tent_le (y y' : ι → ℝ) : |Tent y - Tent y'| ≤ ∑ i, |y i - y' i| := by sorry
