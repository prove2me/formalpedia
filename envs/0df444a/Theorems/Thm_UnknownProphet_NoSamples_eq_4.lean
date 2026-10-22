-- Prove2me | Theorems.Thm_UnknownProphet_NoSamples_eq_4
-- name    : UnknownProphet.NoSamples.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:54.393286+00:00
-- url     : https://prove2.me/theorems/9cd9ea79-ecb1-4dae-884c-4cbf15bfb782
-- title:
--   Equation (4), p. 8 — asymptotic secretary upper bound
-- statement:
--   Let $q_i\in[0,1]$ be arbitrary record-acceptance probabilities. Apply the associated zero-sample rule to a uniformly random permutation of $n$ distinct ranks, and let $P_n(q)$ be its probability of selecting the greatest rank. For every $\delta>0$, there is an $n_0$ depending only on $\delta$ such that
--
--   $$
--   \forall n\ge n_0,\ \forall q\in[0,1]^n,\qquad P_n(q)\le e^{-1}+\delta.
--   $$
--
--   The uniformity in $q$ is needed for the main theorem, where the probabilities come from the rule being challenged.
--
--   **Formalization Note** Uniform permutations of ranks stand for the paper's conditioning on a unique top atom and pairwise distinct draws. The rule and times use zero-based indices.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 8, proof of Theorem 2, equation (4)

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples

/-- Equation (4), p. 8: uniform asymptotic secretary upper bound
for all randomized record rules. -/
theorem eq_4 (δ : ℝ) (hδ : 0 < δ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1),
        recordRuleSuccess q hq ≤ Real.exp (-1) + δ := by sorry

end UnknownProphet.NoSamples
