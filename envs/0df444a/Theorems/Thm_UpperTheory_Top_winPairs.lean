-- Prove2me | Theorems.Thm_UpperTheory_Top_winPairs
-- name    : UpperTheory.Top.winPairs
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:16.165187+00:00
-- url     : https://prove2.me/theorems/f3158bed-4082-447d-9d09-64b0ad52c7ab
-- title:
--   Top: win Pairs
-- statement:
--   The Top construction uses the win Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean#L5-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean#L5-L81

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_WinPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC UpperTheory.Top

theorem UpperTheory.Top.winPairs :
    ∀ (ψ : PChar) (eps c : ℝ), 0 < eps → eps < 1 / 52 → 1 ≤ c → VWinAt ψ 401 → PairEx →
      ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
        ∃ (Y : ℝ) (q d e : ℕ), WinDatum ψ eps J c x Y q d e := by sorry
