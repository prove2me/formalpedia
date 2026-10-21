-- Prove2me | Theorems.Thm_TokenComplexity_Tradeoff_greedy_T
-- name    : TokenComplexity.Tradeoff.greedy_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:12.142172+00:00
-- url     : https://prove2.me/theorems/396b9bb8-41e4-4066-8a6d-e4b0f4ac12ec
-- title:
--   Appendix D, p. 14, T*(α) analogue — minimal knapsack cost for accuracy α is (1/n)·(sum of the ⌈nα⌉ smallest τ's)
-- statement:
--   Let $\tau_1,\dots,\tau_n \in \mathbb N \cup \{\infty\}$, let $\tau_{(1)} \le \tau_{(2)} \le \cdots$ be the finite ones sorted increasingly (ties allowed), and let $A^* = \frac1n \#\{i : \tau_i < \infty\}$. For every $0 \le \alpha \le A^*$, the minimum of $\frac1n\sum_i \tau_i x_i$ over knapsack selections $x \in \{0,1\}^n$ (with $x_i = 1$ only when $\tau_i < \infty$) satisfying $\frac1n\sum_i x_i \ge \alpha$ is attained and equals
--   $$\frac1n \sum_{k=1}^{\lceil n\alpha \rceil} \tau_{(k)}.$$
--
--   This is the greedy solution of the dual problem: to reach accuracy $\alpha$ at least cost, solve the $\lceil n\alpha\rceil$ questions of smallest token complexity.
--
--   **Formalization Note** The range $0 \le \alpha \le A^*$ is added: above $A^*$ no selection is feasible. No distinctness is assumed.
-- source:
--   Lee, Che, Peng, How Well do LLMs Compress Their Own Chain-of-Thought? A Token Complexity Approach, arXiv:2503.01141v2, p. 14, Appendix D, last sentence ("The proof for T*(α) proceeds similarly")

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

namespace TokenComplexity.Tradeoff

open Finset

/-- Appendix D, p. 14, "the proof for T*(α) proceeds similarly": for `0 ≤ α ≤ A*`, the minimal
average cost of a knapsack selection solving at least a fraction `α` of the questions is
`(1/n)` times the sum of the `⌈n α⌉` smallest finite token complexities. Ties are allowed. -/
theorem greedy_T {n : ℕ} (τ : Fin n → ℕ∞) (α : ℝ) (hα0 : 0 ≤ α) (hαA : α ≤ Astar τ) :
    IsLeast {L | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
        α ≤ ((univ.filter (fun i => x i = true)).card : ℝ) / n ∧
        L = (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n}
      ((prefixCost τ ⌈(n : ℝ) * α⌉₊ : ℝ) / n) := by sorry

end TokenComplexity.Tradeoff
