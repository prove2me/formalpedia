-- Prove2me | Theorems.Thm_TokenComplexity_Tradeoff_greedy_alpha
-- name    : TokenComplexity.Tradeoff.greedy_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:08.746921+00:00
-- url     : https://prove2.me/theorems/84a4971d-b953-43b7-8c7a-9ca40b48484a
-- title:
--   Appendix D, p. 14, greedy claim — the unit-reward knapsack optimum is m/n, m the largest affordable number of smallest τ's
-- statement:
--   Let $\tau_1,\dots,\tau_n \in \mathbb N \cup \{\infty\}$ and let $\tau_{(1)} \le \tau_{(2)} \le \dots \le \tau_{(K)}$ be the finite ones, sorted increasingly (ties allowed). For a budget $T \ge 0$ let
--   $$m = \max\Big\{ m \le K : \sum_{k=1}^{m} \tau_{(k)} \le nT \Big\}.$$
--   Then the maximum of $\frac1n \sum_i x_i$ over knapsack selections $x \in \{0,1\}^n$ (with $x_i = 1$ only when $\tau_i < \infty$) satisfying $\frac1n \sum_i \tau_i x_i \le T$ is attained and equals $m/n$.
--
--   This is the greedy solution of the unit-reward knapsack: solve the questions in increasing order of token complexity as long as the budget allows.
--
--   **Formalization Note** No distinctness of the token complexities is assumed; the paper writes $\tau_{(1)} < \dots < \tau_{(n)}$, but the greedy claim holds with ties. The hypothesis $T \ge 0$ is added: for $T < 0$ no selection is feasible. The number $m$ is computed with `Nat.findGreatest`, which returns $0$ when only $m = 0$ qualifies.
-- source:
--   Lee, Che, Peng, How Well do LLMs Compress Their Own Chain-of-Thought? A Token Complexity Approach, arXiv:2503.01141v2, p. 14, Appendix D, paragraph after eq. (12) (the greedy policy)

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

namespace TokenComplexity.Tradeoff

open Finset

/-- Appendix D, p. 14, the greedy claim: for a budget `T ≥ 0`, the optimal value of the unit-reward
knapsack (11)–(12) is `m / n`, where `m` is the largest number of questions such that the `m`
smallest finite token complexities sum to at most `n T`. Ties among token complexities are
allowed. -/
theorem greedy_alpha {n : ℕ} (τ : Fin n → ℕ∞) (T : ℝ) (hT : 0 ≤ T) :
    IsGreatest {a | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
        (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => x i = true)).card : ℝ) / n}
      ((Nat.findGreatest (fun m => (prefixCost τ m : ℝ) ≤ n * T) (sortedFinite τ).length : ℝ)
        / n) := by sorry

end TokenComplexity.Tradeoff
