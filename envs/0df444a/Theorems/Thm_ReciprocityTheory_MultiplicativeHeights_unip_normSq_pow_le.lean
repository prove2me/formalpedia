-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_normSq_pow_le
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_normSq_pow_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:22.111045+00:00
-- url     : https://prove2.me/theorems/d7321ab6-b25f-49a1-8a96-a0414eca344e
-- title:
--   Multiplicative Heights: unip norm Sq pow le
-- statement:
--   The Multiplicative Heights construction uses the unip norm Sq pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L7-L16

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

theorem ReciprocityTheory.MultiplicativeHeights.unip_normSq_pow_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (u : Fin r → ℂ) :
    normSq ((A ^ n) *ᵥ u) ≤ c ^ n * normSq u := by sorry
