-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_hs_le
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_hs_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:13.708255+00:00
-- url     : https://prove2.me/theorems/bc632729-1cab-570c-a7a4-266f1f0db0bc
-- title:
--   Multiplicative Heights: unip hs le
-- statement:
--   The Multiplicative Heights construction uses the unip hs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L43-L53

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

theorem ReciprocityTheory.MultiplicativeHeights.unip_hs_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) :
    ∑ a, ∑ b, ‖A a b‖ ^ 2 ≤ r * c := by sorry
