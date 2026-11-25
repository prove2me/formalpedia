-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_pow_card_eq_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_pow_card_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:01.243794+00:00
-- url     : https://prove2.me/theorems/24d3a881-95af-50a1-b56e-be3363505e93
-- title:
--   Multiplicative Heights: unip pow card eq zero
-- statement:
--   The Multiplicative Heights construction uses the unip pow card eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentA.lean#L36-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentA.lean#L36-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial Matrix

theorem ReciprocityTheory.MultiplicativeHeights.unip_pow_card_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) : N ^ r = 0 := by sorry
