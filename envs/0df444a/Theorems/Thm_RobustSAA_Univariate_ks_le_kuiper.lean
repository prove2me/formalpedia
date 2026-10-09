-- Prove2me | Theorems.Thm_RobustSAA_Univariate_ks_le_kuiper
-- name    : RobustSAA.Univariate.ks_le_kuiper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:05.372872+00:00
-- url     : https://prove2.me/theorems/88ceadb6-735b-43f6-ba7d-753522ff0134
-- title:
--   §10.7, p. 38 — D_N ≤ V_N
-- statement:
--   Let $N\ge1$, let $\xi^1,\dots,\xi^N\in\mathbb R$ have order statistics $\xi^{(1)}\le\dots\le\xi^{(N)}$, and let $F_0$ be a probability distribution on $\mathbb R$. Then the Kolmogorov–Smirnov statistic is at most the Kuiper statistic:
--
--   $$\max_{i}\max\Big\{\tfrac iN-F_0(\xi^{(i)}),\,F_0(\xi^{(i)})-\tfrac{i-1}N\Big\}\le\max_{i}\Big(F_0(\xi^{(i)})-\tfrac{i-1}N\Big)+\max_{i}\Big(\tfrac iN-F_0(\xi^{(i)})\Big).$$
--
--   It transfers the KS argument to the Kuiper test.
--
--   **Formalization Note** Lean indices are 0-based (Lean's `i` is the paper's $i+1$), and the order statistics are the sorted sample `s ∘ Tuple.sort s`. The statement assumes $N\ge1$, which the paper's statistics presuppose.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.7, proof of Theorem 5, p. 38, third paragraph

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

/-- §10.7, p. 38: `D_N ≤ V_N`. -/
theorem ks_le_kuiper {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    ksStat F₀ s ≤ kuiperStat F₀ s := by sorry

end RobustSAA.Univariate
