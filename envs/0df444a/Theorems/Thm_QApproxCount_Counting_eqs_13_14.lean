-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_13_14
-- name    : QApproxCount.Counting.eqs_13_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:10.081802+00:00
-- url     : https://prove2.me/theorems/c8ee4dfb-1be3-41b3-8b68-0e0aa4fea15b
-- title:
--   Eqs. (13)–(14) — Chernoff bound in KL form: Pr[Bin(m, p) ≥ 0.95m] ≤ exp(−m D(95%‖p)) for 0 < p < 0.95
-- statement:
--   Let $0<p<0.95$ and $m\in\mathbb N$, and let $H\sim\mathrm{Bin}(m,p)$ be the number of heads in $m$ tosses of a coin with bias $p$. Then
--   $$\Pr[H\ge0.95\,m]\ \le\ \exp\big(-m\,D(95\%\,\|\,p)\big),$$
--   where $D$ is the Kullback–Leibler divergence of two Bernoulli laws,
--   $$D(95\%\,\|\,p) = 0.95\ln\frac{0.95}{p} + (1-0.95)\ln\frac{1-0.95}{1-p}.$$
--
--   This is the tight form of the Chernoff–Hoeffding bound that the "no early termination" argument for step 1 needs: for small $p$ it decays like $p^{0.95m}$, much faster than the additive Hoeffding bound.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 6, eqs. (13)–(14)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Eqs. (13)–(14), p. 6 (Chernoff–Hoeffding in Kullback–Leibler form): for a coin with bias
`0 < p < 0.95` tossed `m` times, the probability of at least 95% heads is at most
`exp(-m D(95% ‖ p))`, where
`D(95% ‖ p) = 0.95 ln(0.95/p) + (1 - 0.95) ln((1 - 0.95)/(1 - p))`. -/
theorem eqs_13_14 (p : ℝ) (hp : 0 < p) (hp95 : p < 0.95) (m : ℕ) :
    (coin p m).toOuterMeasure {h : ℕ | 0.95 * (m : ℝ) ≤ (h : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) *
        (0.95 * Real.log (0.95 / p) + (1 - 0.95) * Real.log ((1 - 0.95) / (1 - p)))))) := by sorry

end QApproxCount.Counting
