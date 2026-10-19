-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_2_6
-- name    : QApproxCount.Counting.eqs_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:39.401657+00:00
-- url     : https://prove2.me/theorems/5d663920-f727-4952-8401-6972c5ff7aea
-- title:
--   Eqs. (2)–(6) — if k₀ + 1 ≤ k_end ≤ k₀ + 10 then 0.9·1.05^{−k_end} ≤ θ ≤ 1.65·0.9·1.05^{−k_end}
-- statement:
--   Let $\theta>0$ and let $k_0\in\mathbb N$ be the largest integer with $\theta\cdot1.05^{k_0}\le0.9$ (eq. (2)). If $k_0+1\le k_{\mathrm{end}}\le k_0+10$, then
--   $$0.9\cdot1.05^{-k_{\mathrm{end}}} \le \theta \le 1.65\cdot\big(0.9\cdot1.05^{-k_{\mathrm{end}}}\big).$$
--
--   So when step 1 behaves ideally, the bracket $\theta_{\min}=0.9\cdot1.05^{-k_{\mathrm{end}}}$, $\theta_{\max}=1.65\,\theta_{\min}$ that initialises step 2 contains $\theta$.
--
--   **Formalization Note** "$k_0$ is the largest integer with $\theta\cdot1.05^{k_0}\le0.9$" is encoded by the two hypotheses $\theta\cdot1.05^{k_0}\le0.9<\theta\cdot1.05^{k_0+1}$ with $k_0\in\mathbb N$ (in the algorithm $\theta\le0.001$, so $k_0\ge0$).
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 5, eqs. (2)–(6)

import Mathlib

namespace QApproxCount.Counting

/-- Eqs. (2)–(6), p. 5 (ideal case of step 1): let `θ > 0` and let `k₀` be the largest integer
with `θ · 1.05^{k₀} ≤ 0.9`. If `k₀ + 1 ≤ k_end ≤ k₀ + 10`, then
`0.9 · 1.05^{-k_end} ≤ θ ≤ 1.65 · (0.9 · 1.05^{-k_end})`, i.e. `θmin ≤ θ ≤ θmax` for the bracket
initialised in step 2. -/
theorem eqs_2_6 (θ : ℝ) (hθ : 0 < θ) (k₀ kend : ℕ)
    (hk₀ : θ * (1.05 : ℝ) ^ k₀ ≤ 0.9) (hk₀max : 0.9 < θ * (1.05 : ℝ) ^ (k₀ + 1))
    (hlo : k₀ + 1 ≤ kend) (hhi : kend ≤ k₀ + 10) :
    0.9 * (1.05 : ℝ) ^ (-(kend : ℤ)) ≤ θ ∧ θ ≤ 1.65 * (0.9 * (1.05 : ℝ) ^ (-(kend : ℤ))) := by sorry

end QApproxCount.Counting
