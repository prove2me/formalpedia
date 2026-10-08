-- Prove2me | Theorems.Thm_RevenueOrdered_Ratio_sum_ratio_le_one_add_log
-- name    : RevenueOrdered.Ratio.sum_ratio_le_one_add_log
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:05:44.778965+00:00
-- url     : https://prove2.me/theorems/98c5accf-989b-416a-9cd0-76281037c249
-- title:
--   Proof of Theorem 3.2 — ∑_{ℓ=1}^k (r_ℓ − r_{ℓ−1})/r_ℓ ≤ 1 + ln(r_k/r_1)
-- statement:
--   Let $k\ge1$ and let $0<a_1<a_2<\cdots<a_k$ be reals, with $a_0:=0$. Then
--   $$
--   \sum_{\ell=1}^{k}\frac{a_\ell-a_{\ell-1}}{a_\ell}\;=\;1+\sum_{\ell=2}^{k}\frac{a_\ell-a_{\ell-1}}{a_\ell}\;\le\;1+\ln\frac{a_k}{a_1}.
--   $$
--
--   The paper uses this observation, with $a_\ell=r_\ell$ the distinct revenues, to pass from the sum form of Theorem 3.2 to the logarithmic form $1/(1+\ln\rho)$, $\rho=r_k/r_1$. Each term $(a_\ell-a_{\ell-1})/a_\ell$ with $\ell\ge2$ is at most $\int_{a_{\ell-1}}^{a_\ell}dt/t$.
--
--   **Formalization Note** The sequence is a function $a:\mathbb N\to\mathbb R$ with $a_0=0$, $a_1>0$, strictly increasing on $\{1,\dots,k\}$; values beyond $k$ are irrelevant. Both the equality and the inequality of the display are stated.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 9, §3, proof of Theorem 3.2, closing observation

import Mathlib

namespace RevenueOrdered.Ratio

/-- Proof of Theorem 3.2 (p. 9), the closing observation, for any reals
`0 < a_1 < a_2 < ⋯ < a_k` with `a_0 := 0`:
`∑_{ℓ=1}^{k} (a_ℓ − a_{ℓ−1})/a_ℓ = 1 + ∑_{ℓ=2}^{k} (a_ℓ − a_{ℓ−1})/a_ℓ ≤ 1 + ln(a_k/a_1)`. -/
theorem sum_ratio_le_one_add_log (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha1 : 0 < a 1) (hmono : StrictMonoOn a (Set.Icc 1 k)) :
    ∑ l ∈ Finset.Icc 1 k, (a l - a (l - 1)) / a l =
        1 + ∑ l ∈ Finset.Icc 2 k, (a l - a (l - 1)) / a l ∧
      ∑ l ∈ Finset.Icc 1 k, (a l - a (l - 1)) / a l ≤ 1 + Real.log (a k / a 1) := by sorry

end RevenueOrdered.Ratio
