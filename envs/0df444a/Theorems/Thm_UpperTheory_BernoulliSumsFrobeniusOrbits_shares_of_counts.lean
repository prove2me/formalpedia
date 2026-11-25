-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_shares_of_counts
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:07.3847+00:00
-- url     : https://prove2.me/theorems/79740960-fc49-46be-ac63-70cf0f0e7b13
-- title:
--   Bernoulli Sums Frobenius Orbits: shares of counts
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the shares of counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/SharesOfCounts.lean#L6-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/SharesOfCounts.lean#L6-L112

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_SharesOfCounts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts :
    ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (T : Finset A) (δ η D : ℝ),
      0 < δ → η ≤ 1 → 0 ≤ D → 4 * A0.index * D ≤ η * (δ * Nat.card A0) →
      (∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * Nat.card A0| ≤ D) →
      δ * Fintype.card A / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card A ∧
        ∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (T.card : ℝ)| ≤ η * (T.card : ℝ) := by sorry
