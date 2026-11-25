-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_hs_sub_one
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_hs_sub_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:38.17091+00:00
-- url     : https://prove2.me/theorems/51cb8fe5-1743-5fa6-8d4c-6b45a01385aa
-- title:
--   Multiplicative Heights: unip hs sub one
-- statement:
--   The Multiplicative Heights construction uses the unip hs sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L55-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L55-L69

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix

theorem ReciprocityTheory.MultiplicativeHeights.unip_hs_sub_one {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ∑ a, ∑ b, ‖(A - 1) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 - 2 * A.trace.re + r := by sorry
