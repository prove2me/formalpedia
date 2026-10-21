-- Prove2me | Theorems.Thm_TokenComplexity_Tradeoff_eqs_11_12
-- name    : TokenComplexity.Tradeoff.eqs_11_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:12.354372+00:00
-- url     : https://prove2.me/theorems/5acd989b-c2ea-4ca8-af60-058f0c6a6c9a
-- title:
--   Appendix D, eqs. (11)–(12), p. 14 — the token-vector problems equal a unit-reward 0-1 knapsack with costs τ_i
-- statement:
--   Let $\tau_1,\dots,\tau_n \in \mathbb N \cup \{\infty\}$ be token complexities. Call $x \in \{0,1\}^n$ a **knapsack selection** if $x_i = 1$ only for questions with $\tau_i < \infty$. Then:
--
--   1. for every $T$ and $v$, $v$ is the maximum of $\frac1n\sum_i \mathbf 1\{\tau_i \le t_i\}$ over $t \in \mathbb N^n$ with $\frac1n \sum_i t_i \le T$ if and only if $v$ is the maximum of
--   $$\frac1n \sum_{i=1}^n x_i \quad\text{subject to}\quad \frac1n \sum_{i=1}^n \tau_i x_i \le T$$
--   over knapsack selections $x$;
--   2. for every $\alpha$ and $v$, $v$ is the minimum of $\frac1n\sum_i t_i$ over $t\in\mathbb N^n$ with $\frac1n\sum_i \mathbf 1\{\tau_i \le t_i\} \ge \alpha$ if and only if $v$ is the minimum of $\frac1n\sum_i \tau_i x_i$ over knapsack selections with $\frac1n\sum_i x_i \ge \alpha$.
--
--   This identifies the token-budget problem with a 0-1 knapsack in which every question has unit reward and cost $\tau_i$.
--
--   **Formalization Note** The page leaves implicit that a question with $\tau_i = \infty$ cannot be selected ($\tau_i x_i$ would be infinite); this is made explicit in the definition of a knapsack selection. The page states only the $\alpha^*$ problem; the $T^*$ companion, which the proof says "proceeds similarly", is included.
-- source:
--   Lee, Che, Peng, How Well do LLMs Compress Their Own Chain-of-Thought? A Token Complexity Approach, arXiv:2503.01141v2, p. 14, Appendix D, eqs. (11)–(12)

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

namespace TokenComplexity.Tradeoff

open Finset

/-- Appendix D, p. 14, eqs. (11)–(12): the token-vector problems of eqs. (9)–(10) have the same
optimal values as the unit-reward zero-one knapsack over the questions, where selecting question `i`
(`x i = true`) costs `τ i` tokens and is allowed only when `τ i < ∞`. -/
theorem eqs_11_12 {n : ℕ} (τ : Fin n → ℕ∞) :
    (∀ T v : ℝ,
      IsGreatest {a | ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n} v ↔
      IsGreatest {a | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
        (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => x i = true)).card : ℝ) / n} v) ∧
    (∀ α v : ℝ,
      IsLeast {L | ∃ t : Fin n → ℕ,
        α ≤ ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ∧
        L = (∑ i, (t i : ℝ)) / n} v ↔
      IsLeast {L | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
        α ≤ ((univ.filter (fun i => x i = true)).card : ℝ) / n ∧
        L = (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n} v) := by sorry

end TokenComplexity.Tradeoff
