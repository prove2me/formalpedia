-- Prove2me | Theorems.Thm_WeightedMajority_Shifting_Supplement_theorem_7_4
-- name    : WeightedMajority.Shifting.Supplement.theorem_7_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:59:21.658573+00:00
-- url     : https://prove2.me/theorems/744f9664-2ba2-448b-8a66-b2f457cd6c92
-- title:
--   Theorem 7.4 — one recursive class forces the exact floor-log bound
-- statement:
--   There exist an effectively presented domain $X$ and one uniformly computable infinite pool $\phi_1,\phi_2,\ldots:X\to\{0,1\}$ such that, for every $n\ge1$ and every deterministic online prediction algorithm $A$, there are a finite sequence $\mathcal S$ and some $i\le n$ for which $\mathcal S$ is consistent with $\phi_i$ and
--
--   $$M_A(\mathcal S)\ge\lfloor\log_2n\rfloor.$$
--
--   The domain and pool are chosen once, before the prefix length and learner. The witness sequence and target may depend on both. At $n=1$ the conclusion allows the empty sequence and asserts the exact zero lower bound.
--
--   Differences from the source:
--   - encoding: floor of log base 2 for n at least 1 → Nat.log 2 n; reason: Nat.log is the integer floor on this positive domain
--   - encoding: positive pool index i at most n → natural index i strictly below n; reason: index i represents the paper member i+1
--   - encoding: computably indexed total-recursive class → a primitive-codable domain and a Mathlib Computable uncurried evaluator; reason: a single effective evaluation procedure preserves uniform indexing
--   - generalization: every on-line prediction algorithm A (an effective learner, as read in Theorem 7.3) → every function from histories and the current instance to a prediction, computable or not; reason: a lower bound against a larger class of learners contains the source's
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), DOI 10.1006/inco.1994.1009, p. 249, Theorem 7.4

import Definitions.Def_WeightedMajority_Shifting_Supplement_EffectiveBudgets

namespace WeightedMajority.Shifting.Supplement

theorem theorem_7_4 :
    ∃ (X : Type) (_ : Primcodable X) (φ : ℕ → X → Bool),
      Computable (Function.uncurry φ) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : UnderstandingML.OnlineAlg X Bool,
        ∃ (T : ℕ) (S : Fin T → X × Bool) (i : ℕ), i < n ∧
          (∀ t, (S t).2 = φ i (S t).1) ∧
          Nat.log 2 n ≤ UnderstandingML.mistakes A S := by sorry

end WeightedMajority.Shifting.Supplement
