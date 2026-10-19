-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_37_44
-- name    : QApproxCount.Counting.eqs_37_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:43.430037+00:00
-- url     : https://prove2.me/theorems/024f8eb3-d849-43b3-b78c-6f59a19c1034
-- title:
--   Eqs. (37)–(44) — the arithmetico-geometric query sum is O(1/ε) with b = 1/0.9 and T from eq. (30)
-- statement:
--   Let $b:=1/0.9$, $0<\varepsilon\le1$, and $T\in\mathbb N$ with $\ln(b)\,(T+1)\ge\ln(1/\varepsilon)$ (eq. (37)) and $0.65\cdot0.9^T\ge\varepsilon/5$ (eq. (30)). Then
--   $$\sum_{t=0}^{T} b^t\Big[\ln\frac1\varepsilon - t\ln b\Big]\ \le\ \ln(b)\,\frac{b^{T+2}}{(b-1)^2}\ \le\ \frac{3.25\,b^2\ln b}{(b-1)^2\varepsilon}.$$
--
--   The last inequality is the explicit $O(1/\varepsilon)$ conclusion of eq. (44). This bounds the part of the query cost of step 2 that comes from the $\ln(1/\varepsilon)$ term in $\ln\delta_t^{-1}$.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 8, eqs. (37)–(44)

import Mathlib

namespace QApproxCount.Counting

/-- Eqs. (37)–(44), p. 8 (the arithmetico-geometric query sum of step 2): with `b := 1/0.9`,
`0 < ε ≤ 1` and `T` satisfying (30) and (37),
`Σ_{t=0}^{T} b^t [ln(1/ε) - t ln b] ≤ ln(b) b^{T+2} / (b - 1)²`.
The second bound is the explicit `O(1/ε)` conclusion of (44). -/
theorem eqs_37_44 (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (T : ℕ)
    (hT : Real.log (1 / ε) ≤ Real.log (1 / 0.9) * ((T : ℝ) + 1))
    (hTupper : ε / 5 ≤ 0.65 * (0.9 : ℝ) ^ T) :
    ∑ t ∈ Finset.range (T + 1),
        (1 / 0.9 : ℝ) ^ t * (Real.log (1 / ε) - (t : ℝ) * Real.log (1 / 0.9)) ≤
      Real.log (1 / 0.9) * (1 / 0.9 : ℝ) ^ (T + 2) / (1 / 0.9 - 1) ^ 2 ∧
    Real.log (1 / 0.9) * (1 / 0.9 : ℝ) ^ (T + 2) / (1 / 0.9 - 1) ^ 2 ≤
      (Real.log (1 / 0.9) * (1 / 0.9 : ℝ) ^ 2 * 3.25 / (1 / 0.9 - 1) ^ 2) / ε := by sorry

end QApproxCount.Counting
