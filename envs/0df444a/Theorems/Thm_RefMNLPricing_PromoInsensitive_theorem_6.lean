-- Prove2me | Theorems.Thm_RefMNLPricing_PromoInsensitive_theorem_6
-- name    : RefMNLPricing.PromoInsensitive.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:24.92693+00:00
-- url     : https://prove2.me/theorems/93ebacb0-da08-41d2-aaa9-86c882f34ddc
-- title:
--   Theorem 6, p. 24 — if c_i⁻ ≥ c_i⁺ = 0 for all i, the optimal pricing policy admits a steady state
-- statement:
--   Consider the infinite-horizon multi-product pricing problem with reference effects under MNL demand. There are $n$ products with parameters $a_i$, $b_i>0$, $c_i^+,c_i^-\ge0$; the single-period revenue is $\Pi(\mathbf p,\mathbf r)=\sum_i p_i q_i(\mathbf p,\mathbf r)$ with MNL shares $q_i$ driven by the utilities $a_i-b_ip_i+c_i^+(r_i-p_i)_+-c_i^-(p_i-r_i)_+$. Reference prices evolve by exponential smoothing $\mathbf r^{t+1}=\alpha\mathbf r^t+(1-\alpha)\mathbf p^t$ with memory $\alpha\in[0,1]$, revenue is discounted at rate $\beta\in[0,1)$, prices lie in $\mathcal P^n=[0,p_H]^n$ with $p_H>0$ satisfying the standing ceiling assumption $p_H\ge\hat p_H$ of (9), and
--   $$V^\star(\mathbf r^0)=\sup_{(\mathbf p^t)\subset\mathcal P^n}\sum_{t\ge0}\beta^t\,\Pi(\mathbf p^t,\mathbf r^t)$$
--   is the optimal value.
--
--   Suppose consumers are insensitive to the gain effect: $c_i^-\ge c_i^+=0$ for every product $i$. Then the optimal pricing policy admits a steady state: there exists $\mathbf p^{\star\star}\in\mathcal P^n$ such that keeping the price at $\mathbf p^{\star\star}$ forever is optimal when the reference price is $\mathbf p^{\star\star}$,
--   $$V^\star(\mathbf p^{\star\star})\le\frac{\Pi(\mathbf p^{\star\star},\mathbf p^{\star\star})}{1-\beta}.$$
--
--   The result holds for all parameters satisfying the hypotheses: with promotion-insensitive consumers, constant pricing is optimal in the long run. It contrasts with Theorem 4, where a single gain-seeking product rules out any optimal steady state.
--
--   **Formalization Note** Definition 4's "$\mathbf p^\star(\mathbf p^{\star\star})=\mathbf p^{\star\star}$" is stated as optimality of the constant path from reference $\mathbf p^{\star\star}$, because optimal stationary policies need not be unique; under the Bellman equation (6) this is equivalent to some optimal stationary policy fixing $\mathbf p^{\star\star}$. $V^\star$ is the supremum over all admissible price sequences, a genuine (bounded) supremum since $\beta<1$. The hypothesis $c_i^+\le c_i^-$ follows from $c_i^+=0$ and $c_i^-\ge0$ and is kept to mirror the printed chain $c_i^-\ge c_i^+=0$. The standing hypotheses $b>0$, $c^\pm\ge0$, $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$ and the ceiling assumption are those of §2. For $n=0$ the statement holds trivially.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 24, Theorem 6

import Mathlib
import Definitions.Def_RefMNLPricing_PromoInsensitive_Model

namespace RefMNLPricing.PromoInsensitive

/-- Theorem 6, p. 24: if consumers are insensitive to the gain effect, `c_i⁻ ≥ c_i⁺ = 0` for all
`i`, then the optimal pricing policy admits a steady state: there is `p⋆⋆ ∈ [0, p_H]ⁿ` such that
the constant price path `p⋆⋆` is optimal from reference price `p⋆⋆`. -/
theorem theorem_6 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (hgain : ∀ i, cp i = 0) (hloss : ∀ i, cp i ≤ cm i) :
    ∃ x : Fin n → ℝ, RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH x := by sorry

end RefMNLPricing.PromoInsensitive
