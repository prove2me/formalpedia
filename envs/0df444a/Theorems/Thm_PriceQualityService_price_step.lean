-- Prove2me | Theorems.Thm_PriceQualityService_price_step
-- name    : PriceQualityService.price_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:39:35.020905+00:00
-- url     : https://prove2.me/theorems/58f99a71-bb67-4866-903a-88cf3e354416
-- title:
--   Proof of Theorem 1, p. 26 — one-product price step with markup $1+r$
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   Fix a product $i$, its quality $q_i$ and duration $t_i$, and a real number $r$. Put $K_i=c_iq_i^2+t_i(a_i-b_iq_i)$ and
--
--   $$
--   h_i(r,x)=(x-K_i-r)\exp(\alpha_iq_i-x+t_is_i)\qquad(x\in\mathbb R).
--   $$
--
--   Let $\hat p_i=1+r+K_i$. Then
--
--   1. $h_i(r,\cdot)$ is strictly increasing on $(-\infty,\hat p_i]$;
--   2. $h_i(r,\cdot)$ is strictly decreasing on $[\hat p_i,\infty)$;
--   3. $h_i(r,x)\le h_i(r,\hat p_i)$ for every $x$;
--   4. $h_i(r,\hat p_i)=\exp\bigl(\alpha_iq_i-c_iq_i^2+t_i(s_i-(a_i-b_iq_i))-r-1\bigr)$.
--
--   This is the step that produces the equal markup $1+r$ of the optimal MNL prices.
--
--   Differences from the source:
--   - reading: h_i(r, p_i) "is increasing in p_i for p_i ≤ …" and "decreasing thereafter" → StrictMonoOn on (−∞, p̂_i] and StrictAntiOn on [p̂_i, ∞); reason: the derivative [1 − (p_i − K_i − r)]·exp(…) vanishes only at p̂_i; the strict reading is the stronger one
--   - generalization: α_i > 0, s_i > 0, c_i > 0 (pp. 7–8), qualities in the domain of pp. 8–9, t_i ∈ [t_s, t_l] → arbitrary real parameters, qualities and durations; reason: the statement is algebra/calculus that uses none of these assumptions; it specializes to the paper's setting
--   - encoding: products 𝒩 = {1, …, N} → Fin N (N = 0 allowed); reason: Lean convention; N = 0 gives empty sums and changes no instance with N ≥ 1
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), p. 26 (unnumbered, between eqs. (16) and (17))

import Mathlib
import Definitions.Def_PriceQualityService_netValue
import Definitions.Def_PriceQualityService_optPrice

namespace PriceQualityService

/-- **The one-product price step.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), unnumbered, p. 26: with
`h_i(r, p_i) = (p_i − c_i q_i² − t_i(a_i − b_i q_i) − r) · exp(α_i q_i − p_i + t_i s_i)`,
"given r the function `h_i(r,p_i)` is increasing in `p_i` for `p_i ≤ 1 + c_i q_i² + t_i(a_i − b_i q_i) + r`
and is decreasing thereafter. Therefore, it achieves its maximum at
`p_i = 1 + c_i q_i² + t_i(a_i − b_i q_i) + r` and
`h_i(r) = exp(α_i q_i − c_i q_i² + t_i(s_i − (a_i − b_i q_i)) − r − 1)`."

The four clauses: `h_i(r, ·)` is strictly increasing on `(−∞, p̂_i]`, strictly decreasing on
`[p̂_i, ∞)`, maximal at `p̂_i = optPrice a b c q t r i`, with maximum value
`exp(netValue_i − r − 1)`.

**Formalization Note.** "Increasing"/"decreasing" are read strictly (the derivative
`[1 − (p_i − K_i − r)] e^{…}` vanishes only at `p̂_i`). No sign assumption on any parameter. -/
theorem price_step {N : ℕ} (α s a b c q t : Fin N → ℝ) (r : ℝ) (i : Fin N) :
    let h : ℝ → ℝ := fun x =>
      (x - c i * q i ^ 2 - t i * (a i - b i * q i) - r) * Real.exp (α i * q i - x + t i * s i)
    StrictMonoOn h (Set.Iic (optPrice a b c q t r i)) ∧
      StrictAntiOn h (Set.Ici (optPrice a b c q t r i)) ∧
      (∀ x, h x ≤ h (optPrice a b c q t r i)) ∧
      h (optPrice a b c q t r i) = Real.exp (netValue α s a b c q t i - r - 1) := by sorry

end PriceQualityService
