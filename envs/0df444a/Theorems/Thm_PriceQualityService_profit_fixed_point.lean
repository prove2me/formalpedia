-- Prove2me | Theorems.Thm_PriceQualityService_profit_fixed_point
-- name    : PriceQualityService.profit_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:39:04.756681+00:00
-- url     : https://prove2.me/theorems/dfa698dd-d30a-4b27-a301-9ccf53534cdc
-- title:
--   Eq. (15) — profit fixed-point identity
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   For all price, quality and duration vectors, write $\Pi=\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$, $m_i$ for the per-unit margin $p_i-c_iq_i^2-t_i(a_i-b_iq_i)$ and $u_i=\alpha_iq_i-p_i+t_is_i$ for the deterministic utility. Then
--
--   $$
--   \Pi=\sum_{i\in\mathcal N}\bigl(m_i-\Pi\bigr)\exp(u_i).
--   $$
--
--   This rearrangement of the MNL profit is the starting point of the pricing analysis: it turns the profit into a fixed point and lets each product's price be optimized separately.
--
--   Differences from the source:
--   - generalization: α_i > 0, s_i > 0, c_i > 0 (pp. 7–8), qualities in the domain of pp. 8–9, t_i ∈ [t_s, t_l] → arbitrary real parameters, qualities and durations; reason: the statement is algebra/calculus that uses none of these assumptions; it specializes to the paper's setting
--   - encoding: products 𝒩 = {1, …, N} → Fin N (N = 0 allowed); reason: Lean convention; N = 0 gives empty sums and changes no instance with N ≥ 1
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), p. 25, eq. (15)

import Mathlib
import Definitions.Def_PriceQualityService_profit

namespace PriceQualityService

/-- **Eq. (15): the profit fixed-point identity.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 1 (App. B), eq. (15), p. 25:
"Let `Π(p,q,t;𝒩) = r`. Rearranging terms and using some algebra yields
`r = Σ_{i∈𝒩} [p_i − c_i q_i² − t_i(a_i − b_i q_i) − r] · exp(α_i q_i − p_i + t_i s_i)`."

For all prices, qualities and (vector) durations,
`Π = Σ_i (m_i − Π) · exp(u_i)`, where `m_i` is the margin and `u_i` the deterministic utility.

**Formalization Note.** Stated for every parameter vector, with no sign assumptions; the
identity is pure algebra of the MNL formula (2) and the profit (3). -/
theorem profit_fixed_point {N : ℕ} (α s a b c p q t : Fin N → ℝ) :
    profit α s a b c p q t =
      ∑ i, (margin a b c p q t i - profit α s a b c p q t) * Real.exp (utility α s p q t i) := by sorry

end PriceQualityService
