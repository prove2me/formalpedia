-- Prove2me | Theorems.Thm_RefMNLPricing_Gap_myopic_le_opt
-- name    : RefMNLPricing.Gap.myopic_le_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:20.124847+00:00
-- url     : https://prove2.me/theorems/7b92af36-090c-4731-afed-402b5d093923
-- title:
--   §4.1, p. 17 — the myopic value never exceeds the optimal value, V^m(r⁰) ≤ V⋆(r⁰)
-- statement:
--   In the multi-product pricing model with reference effects under MNL demand ($b_i>0$, $c_i^\pm\ge0$, $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$), let $V^\star$ be the optimal value function and let $\mathbf p^m$ be any myopic selection: for every $\mathbf r\in\mathcal P^n=[0,p_H]^n$, $\mathbf p^m(\mathbf r)\in\mathcal P^n$ maximises the single-period revenue $\Pi(\cdot,\mathbf r)$ over $\mathcal P^n$. Let $V^m(\mathbf r^0)=\sum_{t\ge0}\beta^t\Pi(\mathbf p^m(\mathbf r^t),\mathbf r^t)$ be its discounted revenue along $\mathbf r^{t+1}=\alpha\mathbf r^t+(1-\alpha)\mathbf p^m(\mathbf r^t)$.
--
--   Then for every initial reference price $\mathbf r^0\in\mathcal P^n$,
--   $$V^m(\mathbf r^0)\le V^\star(\mathbf r^0).$$
--
--   This is the left inequality of the optimality-gap bound (19); the paper states it as an immediate consequence of the definitions (5) and (8), since the myopic price sequence is admissible.
--
--   **Formalization Note** The inequality is stated for every maximiser selection $\mathbf p^m$, since maximisers of $\Pi(\cdot,\mathbf r)$ need not be unique.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 17, §4.1, first sentence

import Mathlib
import Definitions.Def_RefMNLPricing_Gap_Model

namespace RefMNLPricing.Gap

/-- §4.1, p. 17, first sentence: for every myopic selection `p^m` and every initial reference
price `r⁰ ∈ Pⁿ`, the myopic value is at most the optimal value, `V^m(r⁰) ≤ V⋆(r⁰)`. -/
theorem myopic_le_opt {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm)
    (r₀ : Fin n → ℝ) (hr₀ : RefMNLPricing.Myopic.InBox pH r₀) :
    myopicValue a b cp cm α β pm r₀ ≤ optValue a b cp cm α β pH r₀ := by sorry

end RefMNLPricing.Gap
