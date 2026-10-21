-- Prove2me | Theorems.Thm_TokenComplexity_Tradeoff_eq_8
-- name    : TokenComplexity.Tradeoff.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:03.90684+00:00
-- url     : https://prove2.me/theorems/af392f34-adbf-4254-b255-0ebb415182e6
-- title:
--   Appendix D, eq. (8) (corrected), p. 14 — under Assumption 1, Acc(P) = (1/n) Σ 1{τ_i ≤ t_i(P)}
-- statement:
--   Consider $n$ questions answered by one LLM under a family of prompts, with token lengths $t_i(P)$, correctness indicators $a_i(P)$ and accuracy $\mathrm{Acc}(P) = \frac1n\sum_i a_i(P)$. Suppose Assumption 1 holds with token complexities $\tau_i \in \mathbb N \cup \{\infty\}$. Then for every prompt $P$,
--   $$\mathrm{Acc}(P) = \frac1n \sum_{i=1}^n \mathbf 1\{\tau_i \le t_i(P)\}.$$
--
--   This rewrites the accuracy of a prompt purely in terms of its token lengths, which is the first step of the proof of Theorem 1.
--
--   **Formalization Note** The page prints $\mathbf 1\{\tau_i \ge t_i\}$ in eq. (8); Assumption 1 (p. 5) gives $\mathbf 1\{t_i \ge \tau_i\}$, and the statement follows Assumption 1. A question with $\tau_i = \infty$ never counts.
-- source:
--   Lee, Che, Peng, How Well do LLMs Compress Their Own Chain-of-Thought? A Token Complexity Approach, arXiv:2503.01141v2, p. 14, Appendix D, eq. (8) (sign corrected per Assumption 1, p. 5)

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

namespace TokenComplexity.Tradeoff

open Finset

/-- Appendix D, p. 14, eq. (8) (corrected sign): under Assumption 1 the accuracy of a prompt is the
fraction of questions whose token length reaches their token complexity. -/
theorem eq_8 {n : ℕ} {Prompt : Type} (B : Benchmark n Prompt) (τ : Fin n → ℕ∞)
    (hA1 : TokenComplexityHyp B τ) (P : Prompt) :
    accuracy B P = ((univ.filter (fun i => τ i ≤ (B.len P i : ℕ∞))).card : ℝ) / n := by sorry

end TokenComplexity.Tradeoff
