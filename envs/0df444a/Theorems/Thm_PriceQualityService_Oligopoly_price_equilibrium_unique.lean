-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_price_equilibrium_unique
-- name    : PriceQualityService.Oligopoly.price_equilibrium_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:18:19.81615+00:00
-- url     : https://prove2.me/theorems/28cc2fb3-53f4-4796-91ec-cd6653bbc1e1
-- title:
--   The MNL price competition has a unique equilibrium $p^o_i = \varphi_i(A^o)$
-- statement:
--   Fix quality levels $\mathbf q$ and service durations $\mathbf t$, and write $k_i = c_i q_i^2 + t_i(a_i - b_i q_i)$ and $w_i = \alpha_i q_i + t_i s_i$. Then:
--
--   1. the aggregate equation
--   $$
--   \frac1A + \sum_{j \in \mathcal N} \frac{\exp(w_j - \varphi_j(A))}{A} = 1
--   $$
--   has exactly one positive root $A^o$;
--   2. a price vector $\mathbf p$ is a Nash equilibrium of the price competition (firm $i$ chooses $p_i \in \mathbb R$, with payoff $\Pi_i(\mathbf p, \mathbf q, \mathbf t; \mathcal N)$) if and only if $p_i = \varphi_i(A^o)$ for every $i$.
--
--   In particular the price competition has exactly one Nash equilibrium.
--
--   **Formalization Note** The paper states this at the monopoly qualities and durations $(\mathbf q^*, \mathbf t^*)$; its argument does not use them, and the statement is posed for arbitrary fixed $(\mathbf q, \mathbf t)$, which contains the paper's case.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 3 (PDF p. 36), proof of Theorem 2

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_PriceRoot

namespace PriceQualityService.Oligopoly

/-- Online Supplement p. 3: for fixed quality levels `q` and service durations `t`, the aggregate
equation `1/A + ∑_j exp(α_j q_j − φ_j(A) + t_j s_j)/A = 1` has exactly one positive root `A^o`,
and the price competition has exactly one Nash equilibrium, `p^o_i = φ_i(A^o)`. -/
theorem price_equilibrium_unique {N : ℕ} (α a b c s q t : Fin N → ℝ) :
    ∃ Ao : ℝ, (0 < Ao ∧ IsAggregateRoot α a b c s q t Ao ∧
        ∀ A : ℝ, 0 < A → IsAggregateRoot α a b c s q t A → A = Ao) ∧
      ∀ p : Fin N → ℝ, IsPriceEquilibrium α a b c s q t p ↔
        ∀ i, p i = priceRoot (unitCost a b c q t i) (baseUtility α s q t i) Ao := by sorry

end PriceQualityService.Oligopoly
