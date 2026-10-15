-- Prove2me | Theorems.Thm_SecretaryAdvice_Binary_proposition_12_binary
-- name    : SecretaryAdvice.Binary.proposition_12_binary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:40.80485+00:00
-- url     : https://prove2.me/theorems/97500e5a-1638-43c7-ae71-80a268363b36
-- title:
--   Proposition 12, p. 13 — a monotone optimal greedy dual gives a threshold policy
-- statement:
--   In the binary-advice model, suppose the greedy dual vector is feasible and minimizes the dual LP, and that each of its signal coordinates is non-decreasing in the round number. Then there are signal-dependent thresholds $t_Y,t_N\in\{1,\ldots,n\}$ such that the policy accepting the first best-so-far secretary at or after the threshold for its signal has winning probability at least that of every valid randomized policy:
--
--   $$\Pr(\text{win under }q)\leq\Pr(\text{win under threshold}(t_Y,t_N)).$$
--
--   This is the binary instance of the paper's threshold criterion, which connects the dual LP to an actual stopping policy.
--
--   **Formalization Note** The conclusion competes with every randomized policy based on observed history. The parameter ranges and $n\geq1$ make the finite binary model and thresholds well-defined.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 13, Proposition 12, specialized to Example 5

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_LP

namespace SecretaryAdvice.Binary

/-- Proposition 12, p. 13, applied to Example 5: a monotone optimal greedy dual
solution yields an optimal threshold stopping policy. -/
theorem proposition_12_binary (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1)
    (hopt : DualFeasible n p p' (greedy n p p') ∧
      ∀ u : ℕ → Bool → ℝ, DualFeasible n p p' u →
        dualValue n (greedy n p p') ≤ dualValue n u)
    (hmono : ∀ i : ℕ, 1 ≤ i → i < n → ∀ s : Bool,
      greedy n p p' i s ≤ greedy n p p' (i + 1) s) :
    ∃ tY tN : ℕ, 1 ≤ tY ∧ tY ≤ n ∧ 1 ≤ tN ∧ tN ≤ n ∧
      ∀ q : Policy n, ValidPolicy q →
        win p p' q ≤ win p p' (thresholdPolicy n tY tN) := by sorry

end SecretaryAdvice.Binary
