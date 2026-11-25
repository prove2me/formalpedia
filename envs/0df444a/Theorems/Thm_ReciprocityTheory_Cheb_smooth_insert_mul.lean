-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_smooth_insert_mul
-- name    : ReciprocityTheory.Cheb.smooth_insert_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:30.09781+00:00
-- url     : https://prove2.me/theorems/11f04dd5-39e4-4951-95b7-28bd82b65097
-- title:
--   Cheb: smooth insert mul
-- statement:
--   The Cheb construction uses the smooth insert mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFac.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerFac.lean#L27-L32

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac
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

theorem ReciprocityTheory.Cheb.smooth_insert_mul {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} {b : Ideal (𝓞 E)}
    (q : Prm E) (k : ℕ) (hb : Smooth S b) : Smooth (insert q S) (q.asIdeal ^ k * b) := by sorry
