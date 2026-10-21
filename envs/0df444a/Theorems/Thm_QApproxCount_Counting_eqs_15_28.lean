-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_15_28
-- name    : QApproxCount.Counting.eqs_15_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:08.600466+00:00
-- url     : https://prove2.me/theorems/1b928397-64ef-4bd5-b294-ac6957b8c919
-- title:
--   Eqs. (15)–(28) — the probability that step 1 exits at some round k ≤ k₀ is at most δ/4 (union bound)
-- statement:
--   Let $0<\theta\le0.001$, let $k_0\in\mathbb N$ be the largest integer with $\theta\cdot1.05^{k_0}\le0.9$, let $0<\delta<1$ and $m\ge5000\ln(5/\delta)$, and let $r_k$ be the largest odd integer at most $1.05^k$. If $H_k\sim\mathrm{Bin}\big(m,\sin^2(r_k\theta)\big)$, then
--   $$\sum_{k=0}^{k_0}\Pr[H_k\ge0.95\,m]\ \le\ \delta/4 .$$
--
--   By the union bound, the left-hand side bounds the probability that step 1 terminates too early, at some $k_{\mathrm{end}}\le k_0$.
--
--   **Formalization Note** The printed step (26) has a numerical slip: from (25) as printed, $1.22\cdot0.9^{1.9}\approx0.99867$, not $\le0.9984$. The chain still closes, since $0.99867^{5000}\le e^{-1}$. The statement here is the conclusion (28), which is true.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 6, eqs. (15)–(28)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Eqs. (15)–(28), p. 6 (no early termination): let `0 < θ ≤ 0.001`, let `k₀` be the largest
integer with `θ · 1.05^{k₀} ≤ 0.9`, `0 < δ < 1`, and `m ≥ 5000 ln(5/δ)`. Then the sum over the
rounds `k = 0, …, k₀` of the probability that at least 95% of `m` tosses of a coin with bias
`sin²(r_k θ)` are heads is at most `δ/4` (union bound for exiting step 1 at or before `k₀`). -/
theorem eqs_15_28 (θ δ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 0.001) (k₀ : ℕ)
    (hk₀ : θ * (1.05 : ℝ) ^ k₀ ≤ 0.9) (hk₀max : 0.9 < θ * (1.05 : ℝ) ^ (k₀ + 1))
    (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 5000 * Real.log (5 / δ) ≤ (m : ℝ)) :
    ∑ k ∈ Finset.range (k₀ + 1),
        (coin (Real.sin ((oddFloor k : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} ≤ ENNReal.ofReal (δ / 4) := by sorry

end QApproxCount.Counting
