-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_not_good_le
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.not_good_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:55.256911+00:00
-- url     : https://prove2.me/theorems/2f924ad1-634d-58ae-93b1-f7392a415e9c
-- title:
--   Bernoulli Sums Frobenius Orbits: not good le
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the not good le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/NotGoodLe.lean#L84-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/NotGoodLe.lean#L84-L138

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_TailLe
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_TilesLe
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_NotGoodLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.not_good_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (n L₂ K r u M₀ G' N₁ i₀ : ℕ), (∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 1 ≤ u →
      (M₀ + 1) * ((6 * r + 1) * u) ≤ n →
      exP p ((range n).erase i₀) (fun U => ind (¬ GoodOrbitIntervalTileCondition n (insert i₀ U) L₂ K r u M₀ G' N₁)) ≤
        n * (L₂.choose K : ℝ) * δ ^ K + n * (1 - markedLow δ r u) ^ M₀ + n * binUpper G' δ (N₁ - 1) := by sorry
