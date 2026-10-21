-- Prove2me | Theorems.Thm_TokenComplexity_Tradeoff_eqs_9_10
-- name    : TokenComplexity.Tradeoff.eqs_9_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:08.550245+00:00
-- url     : https://prove2.me/theorems/e349a3b4-5c91-4e93-ae7a-e40adf43e271
-- title:
--   Appendix D, eqs. (9)–(10) (corrected), p. 14 — with rich prompts, α*(T) and T*(α) are optima over token vectors
-- statement:
--   In the setting of the mission, suppose Assumption 1 holds with token complexities $\tau_i \in \mathbb N\cup\{\infty\}$ and the prompts are rich (every token-count vector is realized by some prompt). Then the prompt-level optima reduce to optimization over token-count vectors $t \in \mathbb N^n$:
--
--   1. for every $T$ and $v$, $\alpha^*(T) = v$ if and only if $v$ is the maximum of
--   $$\frac1n \sum_{i=1}^n \mathbf 1\{\tau_i \le t_i\} \quad \text{subject to} \quad \frac1n \sum_{i=1}^n t_i \le T, \ t \in \mathbb N^n;$$
--   2. for every $\alpha$ and $v$, $T^*(\alpha) = v$ if and only if $v$ is the minimum of $\frac1n \sum_i t_i$ over $t \in \mathbb N^n$ with $\frac1n \sum_i \mathbf 1\{\tau_i \le t_i\} \ge \alpha$.
--
--   Here "maximum" and "minimum" mean attained optima. This removes the prompts from the problem, which becomes a finite-dimensional integer program.
--
--   **Formalization Note** The page prints $\mathbf 1\{\tau_i \ge t_i\}$ in (9); the statement uses $\mathbf 1\{\tau_i \le t_i\}$, as Assumption 1 gives. The page states only the $\alpha^*$ problem and says the $T^*$ case "proceeds similarly"; both are included.
-- source:
--   Lee, Che, Peng, How Well do LLMs Compress Their Own Chain-of-Thought? A Token Complexity Approach, arXiv:2503.01141v2, p. 14, Appendix D, eqs. (9)–(10) (sign corrected per Assumption 1, p. 5)

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

namespace TokenComplexity.Tradeoff

open Finset

/-- Appendix D, p. 14, eqs. (9)–(10) (corrected sign): under Assumption 1 and rich prompts, the
optimization over prompts in (3) and (4) becomes an optimization over token-count vectors
`t ∈ ℕⁿ`. -/
theorem eqs_9_10 {n : ℕ} {Prompt : Type} (B : Benchmark n Prompt) (τ : Fin n → ℕ∞)
    (hA1 : TokenComplexityHyp B τ) (hRich : Rich B) :
    (∀ T v : ℝ, IsOptAccuracy B T v ↔
      IsGreatest {a | ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n} v) ∧
    (∀ α v : ℝ, IsMinAvgLen B α v ↔
      IsLeast {L | ∃ t : Fin n → ℕ,
        α ≤ ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ∧
        L = (∑ i, (t i : ℝ)) / n} v) := by sorry

end TokenComplexity.Tradeoff
