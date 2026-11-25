-- Prove2me | Theorems.Thm_UpperTheory_Top_pairHyp
-- name    : UpperTheory.Top.pairHyp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:34.723801+00:00
-- url     : https://prove2.me/theorems/724d393e-3098-4855-bd82-387cfa3941af
-- title:
--   Top: pair Hyp
-- statement:
--   The Top construction uses the pair Hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/PairHyp.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/PairHyp.lean#L24-L35

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_PairHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top

theorem UpperTheory.Top.pairHyp :
    ∀ (eps Y : ℝ) (q d : ℕ), WinPair eps Y q d → HostHyp q d ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1) ∧
      (∀ a : ℕ, Odd a → jacobiSym (-(q : ℤ)) a = jacobiSym (a : ℤ) q ∧ jacobiSym (-(d : ℤ)) a = jacobiSym (a : ℤ) d) := by sorry
