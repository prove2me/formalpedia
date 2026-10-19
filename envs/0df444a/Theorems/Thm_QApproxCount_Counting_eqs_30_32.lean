-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_30_32
-- name    : QApproxCount.Counting.eqs_30_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:38.030037+00:00
-- url     : https://prove2.me/theorems/3f418ab0-49a2-45e5-8a4b-7d27247133ac
-- title:
--   Eqs. (30)–(32) — the failure probabilities δ_t = (δε/65)·0.9^{−t} of rounds t = 0, …, T sum to at most δ/2
-- statement:
--   Let $0<\varepsilon<1$ and $\delta>0$, and let $T\in\mathbb N$ satisfy
--   $$\gamma_T = 0.65\cdot(0.9)^T\ \ge\ \frac{\varepsilon}{5}$$
--   (eq. (30) takes the largest such $T$). With $\delta_t := (\delta\varepsilon/65)\cdot(0.9)^{-t}$,
--   $$\sum_{t=0}^{T}\delta_t\ \le\ \frac{\delta}{2}.$$
--
--   By the union bound over the rounds of step 2 and Lemma 2, step 2 keeps $\theta$ inside its bracket throughout with probability at least $1-\delta/2$.
--
--   **Formalization Note** The statement holds for every $T$ with $0.65\cdot0.9^T\ge\varepsilon/5$, and so in particular for the largest one, which is the $T$ of (30).
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 7, eqs. (30)–(32)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Eqs. (30)–(32), p. 7 (union bound over step 2): for `0 < ε < 1`, `δ > 0` and any `T` with
`γ_T = 0.65 · 0.9^T ≥ ε/5` (in particular the largest such `T`, (30)), the failure
probabilities `δ_t = (δε/65) · 0.9^{-t}` of the rounds `t = 0, …, T` sum to at most `δ/2`. -/
theorem eqs_30_32 (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (T : ℕ)
    (hT : ε / 5 ≤ 0.65 * (0.9 : ℝ) ^ T) :
    ∑ t ∈ Finset.range (T + 1), deltaT ε δ t ≤ δ / 2 := by sorry

end QApproxCount.Counting
