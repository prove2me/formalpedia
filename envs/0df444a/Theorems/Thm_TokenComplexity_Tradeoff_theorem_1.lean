-- Prove2me | Theorems.Thm_TokenComplexity_Tradeoff_theorem_1
-- name    : TokenComplexity.Tradeoff.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:07.500706+00:00
-- url     : https://prove2.me/theorems/e0513262-5239-4ea3-8048-ba2a25f176ac
-- title:
--   Theorem 1 (corrected), p. 7 — under Assumption 1 and rich prompts, α*(T) = (1/n)Σ 1{τ_i ≤ t_T} and T*(α) = (1/n)Σ τ_i 1{τ_i ≤ q_α}
-- statement:
--   Consider $n \ge 1$ questions answered by one LLM under a family of prompts, with accuracy $\mathrm{Acc}(P)$, average token length $\bar t(P)$, and the optima
--   $$\alpha^*(T) = \max_P \{\mathrm{Acc}(P) : \bar t(P) \le T\}, \qquad T^*(\alpha) = \min_P \{\bar t(P) : \mathrm{Acc}(P) \ge \alpha\}.$$
--   Suppose
--
--   1. Assumption 1 holds with token complexities $\tau_i \in \mathbb N\cup\{\infty\}$: question $i$ is answered correctly under $P$ if and only if its chain of thought has at least $\tau_i$ tokens;
--   2. for every token-count vector $(t_i)_{i=1}^n \in \mathbb N^n$ some prompt $P$ produces exactly these token lengths;
--   3. the finite token complexities are pairwise distinct.
--
--   Let $F_n(t) = \frac1n\sum_i \mathbf 1\{\tau_i \le t\}$, $E_n(t) = \frac1n\sum_i \tau_i\mathbf 1\{\tau_i \le t\}$ and $A^* = \frac1n\sum_i \mathbf 1\{\tau_i < \infty\}$. Let $t_T$ be the largest finite $\tau_j$ with $E_n(\tau_j) \le T$, and $q_\alpha$ the smallest finite $\tau_j$ with $F_n(\tau_j) \ge \alpha$ (the α-quantile of the empirical distribution). Then for every $T \ge 0$ and every $0 < \alpha \le A^*$ the optima are attained and
--   $$\alpha^*(T) = \frac1n \sum_{i=1}^n \mathbf 1\{\tau_i \le t_T\}, \qquad T^*(\alpha) = \frac1n \sum_{i=1}^n \tau_i\,\mathbf 1\{\tau_i \le q_\alpha\},$$
--   where the sums run over finite $\tau_i$ and the first sum is $0$ when no finite $\tau_j$ has $E_n(\tau_j) \le T$.
--
--   The theorem gives the exact accuracy–length frontier attainable by any prompting strategy under the token complexity hypothesis: the optimum solves the questions of smallest token complexity first. The paper uses it to compute the lower bound $T^*(A^*)$ on lossless chain-of-thought compression.
--
--   **Formalization Note** The theorem is posed in corrected form. As printed, $t_T \equiv \inf\{t \in \mathbb R : E_n(t) = t\}$ does not involve $T$ and "$t_T = \infty$ if $t > \bar\tau$" uses $t$ for $T$; even the reading $t_T = \sup\{t : E_n(t) \le T\}$ fails ($n = 1$, $\tau = (1)$, $T = 0$ gives $1$ instead of $\alpha^*(0) = 0$). The printed $q_\alpha = \sup\{t : F_n(t) \le \alpha\}$ overshoots ($\tau = (1,2)$, $\alpha = 1/2$ gives $3/2$ instead of $1/2$). The corrected $t_T$ follows the proof's description (p. 14), and $q_\alpha$ the text's ("the α-quantile"). Added hypotheses: $n \ge 1$; $T \ge 0$ (no prompt is feasible otherwise); $0 < \alpha \le A^*$ (above $A^*$ no prompt is feasible; at $\alpha \le 0$ the quantile would pick the smallest $\tau$ instead of giving $0$); pairwise distinct finite token complexities, which the proof uses ("$\tau_{(1)} < \dots < \tau_{(n)}$") and without which the closed form fails ($\tau = (1,1)$, $T = 1/2$: $\alpha^* = 1/2$ but the closed form gives $0$). The LLM is fixed and its superscript $\pi$ dropped.
-- source:
--   Lee, Che, Peng, How Well do LLMs Compress Their Own Chain-of-Thought? A Token Complexity Approach, arXiv:2503.01141v2, p. 7, Theorem 1 (eqs. (5)–(6)); proof in Appendix D, p. 14

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

namespace TokenComplexity.Tradeoff

/-- Theorem 1 (corrected), p. 7: under Assumption 1, rich prompts and pairwise distinct finite token
complexities, `α*(T) = (1/n) ∑ᵢ 1{τᵢ ≤ t_T}` for every budget `T ≥ 0` and
`T*(α) = (1/n) ∑ᵢ τᵢ 1{τᵢ ≤ q_α}` for every `0 < α ≤ A*`, with `t_T` the largest finite `τ_j` with
`E_n(τ_j) ≤ T` and `q_α` the smallest finite `τ_j` with `F_n(τ_j) ≥ α`. -/
theorem theorem_1 {n : ℕ} (hn : 0 < n) {Prompt : Type} (B : Benchmark n Prompt)
    (τ : Fin n → ℕ∞) (hA1 : TokenComplexityHyp B τ) (hRich : Rich B)
    (hdist : ∀ i j, τ i ≠ ⊤ → τ i = τ j → i = j) :
    (∀ T : ℝ, 0 ≤ T → IsOptAccuracy B T (alphaClosed τ T)) ∧
    (∀ α : ℝ, 0 < α → α ≤ Astar τ → IsMinAvgLen B α (TClosed τ α)) := by sorry

end TokenComplexity.Tradeoff
