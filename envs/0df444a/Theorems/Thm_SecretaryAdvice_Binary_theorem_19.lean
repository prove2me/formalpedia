-- Prove2me | Theorems.Thm_SecretaryAdvice_Binary_theorem_19
-- name    : SecretaryAdvice.Binary.theorem_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:48.343876+00:00
-- url     : https://prove2.me/theorems/edcfd146-56ed-463f-bf8a-3c0a33d96d25
-- title:
--   Theorem 19, p. 20 — a binary-advice threshold policy is optimal
-- statement:
--   Consider $n\geq1$ secretaries with uniformly random distinct ranks. The top secretary's binary classifier says $Y$ with probability $p$, and each other secretary's classifier says $N$ with probability $p'$, with $p,p'\in[1/2,1]$ and signals conditionally independent given the ranks. A policy may randomize its stopping decision based on all relative comparisons and signals observed so far. There are thresholds $t_Y,t_N\in\{1,\ldots,n\}$ such that the policy accepting the first best-so-far secretary at or after the threshold for its current signal is optimal:
--
--   $$\Pr(\text{win under }q)\leq\Pr(\text{win under threshold}(t_Y,t_N))\quad\text{for every valid policy }q.$$
--
--   The result shows that the full observed history cannot improve the best achievable success probability beyond a two-threshold rule.
--
--   **Formalization Note** Lean uses zero-based `Fin n` time, while threshold values use the paper's one-based rounds. The existential thresholds precede the universal competitor, so one threshold policy beats every randomized history-dependent policy. The finite winning-probability sum includes the probability of not having stopped earlier.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 20, Theorem 19; model in Example 5, pp. 7–8

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_Setting

namespace SecretaryAdvice.Binary

/-- Theorem 19, p. 20: a threshold policy is optimal against all randomized
history-dependent stopping policies in the binary-classifier model. -/
theorem theorem_19 (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1) :
    ∃ tY tN : ℕ, 1 ≤ tY ∧ tY ≤ n ∧ 1 ≤ tN ∧ tN ≤ n ∧
      ∀ q : Policy n, ValidPolicy q →
        win p p' q ≤ win p p' (thresholdPolicy n tY tN) := by sorry

end SecretaryAdvice.Binary
