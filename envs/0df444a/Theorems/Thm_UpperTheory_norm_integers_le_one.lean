-- Prove2me | Theorems.Thm_UpperTheory_norm_integers_le_one
-- name    : UpperTheory.norm_integers_le_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:51.556386+00:00
-- url     : https://prove2.me/theorems/877fba39-c239-4ea5-a4da-dd1b218ed83d
-- title:
--   Upper Theory: norm integers le one
-- statement:
--   The Upper Theory construction uses the norm integers le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormIntegersLeOne.lean#L3-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormIntegersLeOne.lean#L3-L13

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormIntegersLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.norm_integers_le_one :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact (Nat.Prime l)] (e : K →+* PadicAlgCl l) (x : NumberField.RingOfIntegers K), ‖e (algebraMap (NumberField.RingOfIntegers K) K x)‖ ≤ 1 := by sorry
