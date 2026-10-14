-- Prove2me | Theorems.Thm_RobustSPA_FixedReserve_proposition_5
-- name    : RobustSPA.FixedReserve.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:08.333477+00:00
-- url     : https://prove2.me/theorems/260f5390-606c-4301-8bf1-c18fee83fbbd
-- title:
--   Proposition 5, p. 24 — worst-case regret of SPA(r) over 𝓕_iid, 𝓕_aff, 𝓕_mix; SPA(0) gives ((n−1)/n)ⁿ⁻¹; the best reserve 1/(n+1) gives (n/(n+1))ⁿ
-- statement:
--   Let $n\ge1$ buyers have valuations in $[0,1]^n$, and let $\mathrm{SPA}(r)$ be the second-price auction with fixed deterministic reserve $r$. Write
--   $$W_n(r)=\begin{cases}\max(1-r,\,r), & n=1,\\[2pt] \dfrac{(1-r)^n(n-1)^{n-1}}{((1-r)n-r)^{n-1}}, & n\ge2,\ r\le\tfrac12,\\[4pt] r, & n\ge2,\ r>\tfrac12.\end{cases}$$
--
--   1. For each class $\mathcal F\in\{\mathcal F_{\mathrm{iid}},\mathcal F_{\mathrm{aff}},\mathcal F_{\mathrm{mix}}\}$ and every $r\in[0,1]$, the worst-case regret of $\mathrm{SPA}(r)$ is
--   $$\sup_{\mathbf F\in\mathcal F} R_n(\mathrm{SPA}(r),\mathbf F)=W_n(r).$$
--   2. In particular the second-price auction with no reserve has worst-case regret $W_n(0)=1$ for $n=1$ and $W_n(0)=\big(\frac{n-1}{n}\big)^{n-1}$ for $n\ge2$.
--   3. The reserve minimizing the worst-case regret is $r^*=\frac1{n+1}$, with
--   $$\min_{r\in[0,1]}W_n(r)=W_n\Big(\frac1{n+1}\Big)=\Big(\frac n{n+1}\Big)^n,$$
--   and no other $r\in[0,1]$ attains this minimum.
--
--   This quantifies what is lost by using a deterministic reserve instead of the random reserve of Theorem 1: for every $n$ the best fixed-reserve auction has worst-case regret $(n/(n+1))^n$, above the minimax value over i.i.d. laws.
--
--   **Formalization Note** The worst-case regret is stated as the least upper bound of the set of regrets over the class, not as a maximum: the paper notes (p. 24) that no single distribution attains it, only a sequence of two-point laws with an atom just below the reserve. Reserves are restricted to $r\in[0,1]$, which the page leaves implicit (for $r>1$ the item is never sold and the regret is at most $1<r$). The minimizer's uniqueness renders "the optimal reserve is $r^*$".
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 24, Proposition 5 (proof App-10–11)

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory

namespace RobustSPA.FixedReserve

/-- Proposition 5, p. 24: for each of `𝓕_iid`, `𝓕_aff`, `𝓕_mix` and every reserve
`r ∈ [0,1]`, the worst-case regret of `SPA(r)` (the supremum of its regret over the class,
not attained in general) is `wcFixed n r`; for `SPA(0)` it is `1` if `n = 1` and
`((n−1)/n)^{n−1}` if `n ≥ 2`; and the reserve minimizing it is `r* = 1/(n+1)`, with worst-case
regret `(n/(n+1))ⁿ`. -/
theorem proposition_5 (n : ℕ) (hn : 0 < n) :
    (∀ r ∈ Set.Icc (0 : ℝ) 1,
      IsLUB ((fun μ => regret (SPA (Measure.dirac r)) μ) '' Fiid n) (wcFixed n r) ∧
      IsLUB ((fun μ => regret (SPA (Measure.dirac r)) μ) '' Faff n) (wcFixed n r) ∧
      IsLUB ((fun μ => regret (SPA (Measure.dirac r)) μ) '' Fmix n) (wcFixed n r)) ∧
    wcFixed n 0 = (if n = 1 then 1 else (((n : ℝ) - 1) / n) ^ (n - 1)) ∧
    IsLeast (wcFixed n '' Set.Icc 0 1) (((n : ℝ) / (n + 1)) ^ n) ∧
    wcFixed n (1 / (n + 1)) = ((n : ℝ) / (n + 1)) ^ n ∧
    ∀ r ∈ Set.Icc (0 : ℝ) 1, wcFixed n r = ((n : ℝ) / (n + 1)) ^ n → r = 1 / (n + 1) := by sorry

end RobustSPA.FixedReserve
