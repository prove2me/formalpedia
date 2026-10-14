-- Prove2me | Theorems.Thm_RefMNLPricing_Gap_proposition_2
-- name    : RefMNLPricing.Gap.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:15.116993+00:00
-- url     : https://prove2.me/theorems/062929a0-f61c-4871-9b85-2043ae6df909
-- title:
--   Proposition 2, p. 17 — optimality gap 0 ≤ V⋆(r⁰) − V^m(r⁰) ≤ β(1−α)ωp_H/((1−αβ)(1−β))
-- statement:
--   Consider $n$ products with MNL demand and reference effects: intrinsic utilities $a_i$, price sensitivities $b_i>0$, reference sensitivities $c_i^+\ge0$ (gains) and $c_i^-\ge0$ (losses), memory parameter $\alpha\in[0,1]$, discount factor $\beta\in[0,1)$, and price ceiling $p_H>0$ with admissible box $\mathcal P^n=[0,p_H]^n$. Assume the paper's standing ceiling condition $p_H\ge\hat p_H$, where $\hat p_H$ is the root of equation (9). Let $V^\star$ be the optimal value function, let $\mathbf p^m$ be any myopic pricing policy (a selection of maximisers of the single-period revenue $\Pi(\cdot,\mathbf r)$ over $\mathcal P^n$), and let $V^m$ be its discounted revenue. Set
--   $$\omega=\max_{i\in N}\Big\{\frac{c_i^+}{b_i+c_i^+},\ \frac{c_i^-}{b_i+c_i^-}\Big\}.$$
--
--   Then for every initial reference price $\mathbf r^0\in\mathcal P^n$,
--   $$0\le V^\star(\mathbf r^0)-V^m(\mathbf r^0)\le\frac{\beta(1-\alpha)}{(1-\alpha\beta)(1-\beta)}\cdot\omega\,p_H.$$
--
--   The bound is uniform in the initial reference price and vanishes when $\alpha=1$, $\beta=0$ or $\omega=0$. It makes the myopic policy, which only needs a single-period optimisation, a policy with an explicit performance guarantee against the intractable optimal policy.
--
--   **Formalization Note** The bound is stated for every myopic selection, since the single-period maximiser need not be unique. The ceiling condition is the paper's standing assumption of §2.4 (p. 11) for §3–§4 and is a hypothesis here. $\omega$ is written `⨆ i` over `Fin n`, which is $0$ when $n=0$ (then both values are $0$). $V^\star$ is the supremum over admissible price sequences; the Bellman equation (6) for it is a separate milestone.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 17, Proposition 2, display (19); standing assumption §2.4, p. 11

import Mathlib
import Definitions.Def_RefMNLPricing_Gap_Model

namespace RefMNLPricing.Gap

/-- Proposition 2 (Optimality Gap), p. 17, display (19): under the standing assumptions, including
the ceiling assumption `p_H ≥ p̂_H` of §2.4, for every myopic selection `p^m` and every initial
reference price `r⁰ ∈ Pⁿ`,
`0 ≤ V⋆(r⁰) − V^m(r⁰) ≤ β(1 − α)/((1 − αβ)(1 − β)) · ω p_H`,
where `ω = max_i {c_i⁺/(b_i + c_i⁺), c_i⁻/(b_i + c_i⁻)}`. -/
theorem proposition_2 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm)
    (r₀ : Fin n → ℝ) (hr₀ : RefMNLPricing.Myopic.InBox pH r₀) :
    0 ≤ optValue a b cp cm α β pH r₀ - myopicValue a b cp cm α β pm r₀ ∧
      optValue a b cp cm α β pH r₀ - myopicValue a b cp cm α β pm r₀ ≤
        β * (1 - α) / ((1 - α * β) * (1 - β)) * omega b cp cm * pH := by sorry

end RefMNLPricing.Gap
