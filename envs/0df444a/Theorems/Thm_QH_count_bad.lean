-- Prove2me | Theorems.Thm_QH_count_bad
-- name    : QH.count_bad
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:48.634207+00:00
-- url     : https://prove2.me/theorems/aece8fae-d80c-4fa2-9ee6-c8d289887c39
-- title:
--   QH: count bad
-- statement:
--   The QH construction uses the count bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean#L9-L16

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZAll
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_CountBadCore
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_CountBad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH

theorem QH.count_bad :
    ∃ C : ℝ, ∀ (Q F : ℝ) (B : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ B, q.Prime ∧ F < q ∧ ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox Q ψ) → (B.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by sorry
