-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_7_12
-- name    : QApproxCount.Counting.eqs_7_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:10.24873+00:00
-- url     : https://prove2.me/theorems/50f09f60-2bae-4ba4-a48b-d5b1754181d7
-- title:
--   Eqs. (7)–(12) — at round k₀ + 10 the bias is ≥ 0.96 and step 1 fails to exit with probability ≤ δ/5
-- statement:
--   Let $0<\theta\le0.001$, let $k_0\in\mathbb N$ be the largest integer with $\theta\cdot1.05^{k_0}\le0.9$, let $\delta>0$, and let $m\ge5000\ln(5/\delta)$. Let $r_{k}$ be the largest odd integer at most $1.05^{k}$. Then
--   $$\sin^2(r_{k_0+10}\,\theta)\ \ge\ 0.96,$$
--   and if $H\sim\mathrm{Bin}\big(m,\sin^2(r_{k_0+10}\theta)\big)$ counts the marked outcomes of round $k_0+10$, then
--   $$\Pr[H<0.95\,m]\ \le\ \delta/5 .$$
--
--   This is the "no late termination" half of the correctness of step 1: if step 1 reaches round $k_0+10$ it exits there with probability at least $1-\delta/5$.
--
--   **Formalization Note** The failure event is $H<0.95m$, the negation of the exit test $H\ge0.95m$ of step 1(b). The paper writes "$\le 95\%$" in (10). The printed chain (8) has the slip $0.9\cdot1.05^{10}\ge1.396$ at its lower end; the correct value is $0.9\cdot1.05^{9}\approx1.3962$. The conclusion is unchanged.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 5, eqs. (7)–(12)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Eqs. (7)–(12), p. 5 (no late termination): let `0 < θ ≤ 0.001`, let `k₀` be the largest
integer with `θ · 1.05^{k₀} ≤ 0.9`, `δ > 0`, and `m ≥ 5000 ln(5/δ)` tosses. Then the coin of
round `k₀ + 10` has bias `sin²(r_{k₀+10} θ) ≥ 0.96`, and the probability that fewer than 95% of
`m` tosses of that coin are heads (step 1 fails to exit at `k₀ + 10`) is at most `δ/5`. -/
theorem eqs_7_12 (θ δ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 0.001) (k₀ : ℕ)
    (hk₀ : θ * (1.05 : ℝ) ^ k₀ ≤ 0.9) (hk₀max : 0.9 < θ * (1.05 : ℝ) ^ (k₀ + 1))
    (hδ : 0 < δ) (m : ℕ) (hm : 5000 * Real.log (5 / δ) ≤ (m : ℝ)) :
    0.96 ≤ Real.sin ((oddFloor (k₀ + 10) : ℝ) * θ) ^ 2 ∧
      (coin (Real.sin ((oddFloor (k₀ + 10) : ℝ) * θ) ^ 2) m).toOuterMeasure
          {h : ℕ | (h : ℝ) < 0.95 * (m : ℝ)} ≤ ENNReal.ofReal (δ / 5) := by sorry

end QApproxCount.Counting
