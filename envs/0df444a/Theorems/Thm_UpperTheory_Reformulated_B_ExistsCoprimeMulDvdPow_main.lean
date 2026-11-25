-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ExistsCoprimeMulDvdPow_main
-- name    : UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:24:11.162853+00:00
-- url     : https://prove2.me/theorems/6e901334-54b8-5b8b-9008-b0e889e5edb6
-- title:
--   Exists Coprime Mul Dvd Pow: main
-- statement:
--   The Exists Coprime Mul Dvd Pow construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/KeyLemmaStatement.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/KeyLemmaStatement.lean#L33-L38

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KeyLemmaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main :
    ∀ (g m : ℕ),
    (0 : ℕ) < m → ∃ (c : ℕ) (d : ℕ), m = c * d ∧ c.Coprime g ∧ d ∣ g ^ m := by sorry
