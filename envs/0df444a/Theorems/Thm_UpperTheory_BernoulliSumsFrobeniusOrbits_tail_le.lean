-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_tail_le
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.tail_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:21.203788+00:00
-- url     : https://prove2.me/theorems/60fe243a-3c13-4978-9cde-11f98541bb9d
-- title:
--   Bernoulli Sums Frobenius Orbits: tail le
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the tail le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/TailLe.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/TailLe.lean#L30-L41

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_TailLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.tail_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (A : Finset ℕ) (G K : ℕ), (∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → A.card ≤ G →
      exP p A (fun T => ind (K ≤ T.card)) ≤ (G.choose K : ℝ) * δ ^ K ∧ exP p A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by sorry
