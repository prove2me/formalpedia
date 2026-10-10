-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_equilibrium_price_le
-- name    : PriceQualityService.Oligopoly.equilibrium_price_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:18:12.920841+00:00
-- url     : https://prove2.me/theorems/99a56335-4889-41c9-aee7-e54be4fe9d0a
-- title:
--   Equilibrium prices are at most the monopoly prices: $\varphi_i(A^o) \le m^* + k_i$
-- statement:
--   Fix quality levels $\mathbf q$ and durations $\mathbf t$, and write $k_i = c_i q_i^2 + t_i(a_i - b_i q_i)$. Let $A^o > 0$ be a root of the aggregate equation and $m^*$ the solution of $m = 1 + \sum_i \exp(\alpha_i q_i - c_i q_i^2 - t_i(a_i - b_i q_i - s_i) - m)$. Then for every product $i$
--   $$
--   p_i^o = \varphi_i(A^o) \le m^* + c_i q_i^2 + t_i(a_i - b_i q_i).
--   $$
--
--   At the monopoly qualities and durations, the right-hand side is the monopoly price $p_i^*$ (Theorem 1(c)), so equilibrium prices are no higher than monopoly prices.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 3 (PDF p. 36), proof of Theorem 2

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_PriceRoot

namespace PriceQualityService.Oligopoly

/-- Online Supplement p. 3: with `A^o` the positive root of the aggregate equation and `m*` the
root of `m = 1 + ∑_i exp(α_i q_i − c_i q_i² − t_i(a_i − b_i q_i − s_i) − m)`, every equilibrium
price satisfies `p^o_i = φ_i(A^o) ≤ m* + c_i q_i² + t_i(a_i − b_i q_i)`. -/
theorem equilibrium_price_le {N : ℕ} (α a b c s q t : Fin N → ℝ) (Ao m : ℝ) (hAo : 0 < Ao)
    (hA : IsAggregateRoot α a b c s q t Ao)
    (hm : m = 1 + ∑ i, Real.exp (α i * q i - c i * q i ^ 2 - t i * (a i - b i * q i - s i) - m))
    (i : Fin N) :
    priceRoot (unitCost a b c q t i) (baseUtility α s q t i) Ao ≤ m + unitCost a b c q t i := by sorry

end PriceQualityService.Oligopoly
