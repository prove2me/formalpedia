-- Prove2me | Theorems.Thm_PriceQualityService_price_optimized_profit
-- name    : PriceQualityService.price_optimized_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:40:38.594629+00:00
-- url     : https://prove2.me/theorems/26c30be2-c4bc-41e7-b1b9-22b49510abb9
-- title:
--   Eq. (17) — the price-optimized profit is the root $r$
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   Fix quality and duration vectors $\mathbf q,\mathbf t$, and let $r$ satisfy
--
--   $$
--   r=\sum_{i\in\mathcal N}\exp\Bigl(\alpha_iq_i-c_iq_i^2+t_i\bigl(s_i-(a_i-b_iq_i)\bigr)-r-1\Bigr).
--   $$
--
--   Then
--
--   1. $\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)\le r$ for every price vector $\mathbf p\in\mathbb R^N$, and
--   2. the equal-markup prices $\hat p_i=1+r+c_iq_i^2+t_i(a_i-b_iq_i)$ attain $\Pi(\hat{\mathbf p},\mathbf q,\mathbf t;\mathcal N)=r$.
--
--   So $\max_{\mathbf p}\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)=r$: the price-optimized MNL profit is the root of eq. (17), and it is attained at the equal-markup prices.
--
--   Differences from the source:
--   - encoding: "problem max_p Π(p,q,t;N) becomes r = Σ exp(…)" → for r solving (17): Π(p, q, t) ≤ r for all p, and Π(optPrice, q, t) = r; reason: this is what "the maximum over prices equals r" means, stated without a supremum; the root exists by root_exists_unique
--   - generalization: α_i > 0, s_i > 0, c_i > 0 (pp. 7–8), qualities in the domain of pp. 8–9, t_i ∈ [t_s, t_l] → arbitrary real parameters, qualities and durations; reason: the statement is algebra/calculus that uses none of these assumptions; it specializes to the paper's setting
--   - encoding: products 𝒩 = {1, …, N} → Fin N (N = 0 allowed); reason: Lean convention; N = 0 gives empty sums and changes no instance with N ≥ 1
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), p. 26, eq. (17)

import Mathlib
import Definitions.Def_PriceQualityService_profit
import Definitions.Def_PriceQualityService_netValue
import Definitions.Def_PriceQualityService_optPrice

namespace PriceQualityService

/-- **Eq. (17): the price-optimized profit is the root `r`.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), eq. (17), p. 26: "Immediately, problem `max_p Π(p,q,t;𝒩)`
becomes `r = Σ_{i∈𝒩} exp(α_i q_i − c_i q_i² + t_i(s_i − (a_i − b_i q_i)) − r − 1)`."

Fix qualities `q` and (vector) durations `t`, and let `r` solve
`r = Σ_i exp(netValue_i − r − 1)`. Then `Π(p, q, t) ≤ r` for every price vector `p`, and the
equal-markup price `p_i = 1 + r + c_i q_i² + t_i(a_i − b_i q_i)` attains `Π = r`. So
`max_p Π(p, q, t) = r`.

**Formalization Note.** Prices range over all of `ℝ^N`. The root enters as a hypothesis; it
exists and is unique by `root_exists_unique`. No sign assumptions. -/
theorem price_optimized_profit {N : ℕ} (α s a b c q t : Fin N → ℝ) (r : ℝ)
    (hr : r = ∑ i, Real.exp (netValue α s a b c q t i - r - 1)) :
    (∀ p : Fin N → ℝ, profit α s a b c p q t ≤ r) ∧
      profit α s a b c (optPrice a b c q t r) q t = r := by sorry

end PriceQualityService
