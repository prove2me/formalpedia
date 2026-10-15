-- Prove2me | Theorems.Thm_RefMNLPricing_PromoInsensitive_observation_p24
-- name    : RefMNLPricing.PromoInsensitive.observation_p24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:18.09768+00:00
-- url     : https://prove2.me/theorems/68105fbc-5286-44ff-a201-3fb39dfe344f
-- title:
--   §4.2.1, p. 24 — under c_i⁺ = 0 a myopic fixed point p⋆⋆ attains max_{p,r∈Pⁿ} Π(p, r)
-- statement:
--   Consider the multi-product MNL pricing model with reference effects: $n$ products with parameters $a_i$, $b_i>0$, $c_i^+,c_i^-\ge 0$, utilities $u_i(\mathbf p,\mathbf r)=a_i-b_ip_i+c_i^+(r_i-p_i)_+-c_i^-(p_i-r_i)_+$, MNL shares $q_i$ and single-period revenue $\Pi(\mathbf p,\mathbf r)=\sum_i p_i q_i(\mathbf p,\mathbf r)$. Prices and reference prices range over the box $\mathcal P^n=[0,p_H]^n$, $p_H>0$, and the price ceiling satisfies the standing assumption $p_H\ge\hat p_H$, where $\hat p_H$ solves (9).
--
--   Suppose consumers are insensitive to promotions: $c_i^+=0$ for every product $i$. Then there exists $\mathbf p^{\star\star}\in\mathcal P^n$ such that
--
--   1. $\mathbf p^{\star\star}$ is a fixed point of the myopic policy: $\Pi(\mathbf p,\mathbf p^{\star\star})\le\Pi(\mathbf p^{\star\star},\mathbf p^{\star\star})$ for every $\mathbf p\in\mathcal P^n$;
--   2. $(\mathbf p^{\star\star},\mathbf p^{\star\star})$ attains the highest possible single-period revenue:
--   $$\Pi(\mathbf p,\mathbf r)\le\Pi(\mathbf p^{\star\star},\mathbf p^{\star\star})\qquad\text{for all }\mathbf p,\mathbf r\in\mathcal P^n .$$
--
--   This is the observation on which the authors base the proof of Theorem 6: a price that is simultaneously the best response to itself as a reference and the best single-period revenue over all price/reference pairs. Note that with $c^+=0$ the revenue is not monotone in the reference price in an obvious way, because lowering one product's utility can raise the MNL revenue when its price is below $\Pi$; joint maximality is a genuine claim.
--
--   **Formalization Note** "$\mathbf p^m(\mathbf p^{\star\star})=\mathbf p^{\star\star}$" is stated as "$\mathbf p^{\star\star}$ is a maximiser of $\Pi(\cdot,\mathbf p^{\star\star})$ over $\mathcal P^n$", since the myopic maximiser need not be unique and the paper fixes no selection; item 1 is the special case $\mathbf r=\mathbf p^{\star\star}$ of item 2 and is kept to mirror the sentence. The standing hypotheses $b>0$, $c^\pm\ge0$, $p_H>0$ and the ceiling assumption (§2.4, p. 11) are taken from the page's section; without the ceiling the maximiser may lie on the boundary of the box. The memory and discount parameters play no role.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 24, §4.2.1, last paragraph

import Mathlib
import Definitions.Def_RefMNLPricing_PromoInsensitive_Model

namespace RefMNLPricing.PromoInsensitive

/-- §4.2.1, p. 24, last paragraph: when consumers are insensitive to promotions (`c_i⁺ = 0` for
all `i`), there is `p⋆⋆ ∈ [0, p_H]ⁿ` that is a myopic fixed point (a maximiser of `Π(·, p⋆⋆)` over
the box) and such that `(p⋆⋆, p⋆⋆)` maximises `Π(p, r)` jointly over `p, r ∈ [0, p_H]ⁿ`. -/
theorem observation_p24 {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (hgain : ∀ i, cp i = 0) :
    ∃ x : Fin n → ℝ, RefMNLPricing.Myopic.InBox pH x ∧
      (∀ p, RefMNLPricing.Myopic.InBox pH p → RefMNLPricing.Myopic.revenue a b cp cm p x ≤ RefMNLPricing.Myopic.revenue a b cp cm x x) ∧
      (∀ p r, RefMNLPricing.Myopic.InBox pH p → RefMNLPricing.Myopic.InBox pH r → RefMNLPricing.Myopic.revenue a b cp cm p r ≤ RefMNLPricing.Myopic.revenue a b cp cm x x) := by sorry

end RefMNLPricing.PromoInsensitive
