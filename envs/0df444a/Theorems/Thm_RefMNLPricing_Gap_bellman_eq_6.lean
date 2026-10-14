-- Prove2me | Theorems.Thm_RefMNLPricing_Gap_bellman_eq_6
-- name    : RefMNLPricing.Gap.bellman_eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:15.790537+00:00
-- url     : https://prove2.me/theorems/0d759d5c-291e-467b-9ebb-54c0b10031bd
-- title:
--   (6), p. 9 — the optimal value V⋆ satisfies the Bellman equation with an attained maximum
-- statement:
--   Consider the multi-product pricing model with reference effects under MNL demand: $n$ products with parameters $a_i$, $b_i>0$, $c_i^+\ge0$, $c_i^-\ge0$, memory parameter $\alpha\in[0,1]$, discount factor $\beta\in[0,1)$, price ceiling $p_H>0$ and admissible box $\mathcal P^n=[0,p_H]^n$. Let $\Pi(\mathbf p,\mathbf r)$ be the single-period MNL revenue and let $V^\star$ be the optimal value function, the supremum of $\sum_{t\ge0}\beta^t\Pi(\mathbf p^t,\mathbf r^t)$ over all admissible price sequences along $\mathbf r^{t+1}=\alpha\mathbf r^t+(1-\alpha)\mathbf p^t$.
--
--   Then for every initial reference price $\mathbf r^0\in\mathcal P^n$, $V^\star$ satisfies the Bellman equation
--   $$V^\star(\mathbf r^0)=\max_{\mathbf p\in\mathcal P^n}\Big\{\Pi(\mathbf p,\mathbf r^0)+\beta\,V^\star\big(\alpha\mathbf r^0+(1-\alpha)\mathbf p\big)\Big\},$$
--   and the maximum is attained: there is an optimal price $\mathbf p^\star(\mathbf r^0)\in\mathcal P^n$ with $V^\star(\mathbf r^0)=\Pi(\mathbf p^\star(\mathbf r^0),\mathbf r^0)+\beta V^\star(\alpha\mathbf r^0+(1-\alpha)\mathbf p^\star(\mathbf r^0))$.
--
--   This is the equation (6) through which the paper uses $V^\star$; it identifies the supremum over price sequences with the value of the paper's dynamic program and provides an optimal stationary pricing policy.
--
--   **Formalization Note** The statement is `IsGreatest` of the set of values $\Pi(\mathbf p,\mathbf r^0)+\beta V^\star(\alpha\mathbf r^0+(1-\alpha)\mathbf p)$, $\mathbf p\in\mathcal P^n$: $V^\star(\mathbf r^0)$ belongs to the set (attainment) and bounds it from above. The paper's standing price-ceiling assumption $p_H\ge\hat p_H$ is not needed for (6) and is omitted, so this statement is more general than its use in the paper.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 9, display (6)

import Mathlib
import Definitions.Def_RefMNLPricing_Gap_Model

namespace RefMNLPricing.Gap

/-- The Bellman equation (6), p. 9: for every initial reference price `r⁰ ∈ Pⁿ`, the optimal value
`V⋆(r⁰)` is the maximum over `p ∈ Pⁿ` of `Π(p, r⁰) + β V⋆(α r⁰ + (1 − α) p)`, and the maximum is
attained (an optimal price `p⋆(r⁰)` exists). -/
theorem bellman_eq_6 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (r₀ : Fin n → ℝ) (hr₀ : RefMNLPricing.Myopic.InBox pH r₀) :
    IsGreatest
      {v : ℝ | ∃ p : Fin n → ℝ, RefMNLPricing.Myopic.InBox pH p ∧
        v = RefMNLPricing.Myopic.revenue a b cp cm p r₀ +
          β * optValue a b cp cm α β pH (fun i => α * r₀ i + (1 - α) * p i)}
      (optValue a b cp cm α β pH r₀) := by sorry

end RefMNLPricing.Gap
