-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_csb_pow_le
-- name    : ReciprocityTheory.Cheb.csb_pow_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:12.120827+00:00
-- url     : https://prove2.me/theorems/e9415f20-38d1-5521-9a2b-a4f448de28de
-- title:
--   Cheb: csb pow le
-- statement:
--   The Cheb construction uses the csb pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitB.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitB.lean#L14-L23

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.csb_pow_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ^ 2 ≤ b) (s : ℝ) (hs : 1 < s) :
    ((b : ℕ) : ℝ) ^ (-s) ≤ ((a : ℕ) : ℝ) ^ (-2 : ℝ) := by sorry
