-- Prove2me | Theorems.Thm_RobustSAA_Univariate_levy_le_ks
-- name    : RobustSAA.Univariate.levy_le_ks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:01.275592+00:00
-- url     : https://prove2.me/theorems/300f3e2e-0d9c-435d-86d1-c77cda0f4f34
-- title:
--   §10.7, p. 38 — d_Lévy(F̂_N, F₀) ≤ D_N(F₀)
-- statement:
--   Let $N\ge1$, let $\xi^1,\dots,\xi^N\in\mathbb R$ be any data with order statistics $\xi^{(1)}\le\dots\le\xi^{(N)}$ and empirical cdf $\hat F_N$, and let $F_0$ be any probability distribution on $\mathbb R$. With the Kolmogorov–Smirnov statistic $D_N(F_0)=\max_{i}\max\{\tfrac iN-F_0(\xi^{(i)}),\,F_0(\xi^{(i)})-\tfrac{i-1}N\}$,
--
--   $$d_{\text{Lévy}}(\hat F_N,F_0)\le D_N(F_0).$$
--
--   This bounds the Lévy distance between the empirical cdf and any distribution in the KS confidence region by the KS threshold, which is how uniform consistency of the KS and Kuiper tests is obtained.
--
--   **Formalization Note** Lean indices are 0-based (Lean's `i` is the paper's $i+1$), and the order statistics are the sorted sample `s ∘ Tuple.sort s`. The statement assumes $N\ge1$, which the paper's statistics presuppose.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.7, proof of Theorem 5, p. 38, third paragraph

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

/-- §10.7, p. 38: `d_Lévy(F̂_N, F₀) ≤ D_N(F₀)`. -/
theorem levy_le_ks {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    levyDist (empCdf s) (cdfOf F₀) ≤ ksStat F₀ s := by sorry

end RobustSAA.Univariate
