-- Prove2me | Theorems.Thm_RefMNLPricing_Myopic_theorem_3_convergence
-- name    : RefMNLPricing.Myopic.theorem_3_convergence
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T19:30:00.511647+00:00
-- url     : https://prove2.me/theorems/a1a59aaa-dbdb-46ce-a600-cdb52ebbb025
-- title:
--   Theorem 3.1, p. 15 — without gain-seeking products the myopic price path converges
-- statement:
--   Consider the MNL pricing model with reference effects of Guo, Jiang and Shen: products $i\in N$ with $a_i\in\mathbb R$, $b_i>0$, $c_i^+,c_i^-\ge 0$, memory $\alpha\in[0,1]$, price box $\mathcal P^n=[0,p_H]^n$ with $p_H>0$, and the standing ceiling assumption $p_H\ge \hat p_H$ (with $\hat p_H$ a root of equation (9)). Let $p^m$ be any myopic pricing policy, i.e. for every $r\in\mathcal P^n$ the vector $p^m(r)$ maximises the single-period revenue $\Pi(\cdot,r)$ over $\mathcal P^n$, and for $r^0\in\mathcal P^n$ let
--
--   $$
--   r^{t+1}=\alpha r^t+(1-\alpha)\,p^m(r^t),\qquad t\ge 0 .
--   $$
--
--   **Claim.** If no product is gain-seeking, i.e. $c_i^+\le c_i^-$ for every $i$ ($N_g=\emptyset$), then the myopic price path $\{p^m(r^t)\}_{t\ge0}$ converges in $\mathbb R^n$.
--
--   This is the convergence half of part 1 of Theorem 3 (p. 15). The remaining assertions of part 1 (the limit lies in $\mathcal P^n$, and for $\alpha<1$ it is a steady state $p^m(L)=L$) follow from this convergence together with Theorem 2: the reference path then converges to the same limit $L$, the argmax correspondence has closed graph so $L$ maximises $\Pi(\cdot,L)$, and without gain-seeking products Theorem 2 makes the maximiser unique.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 15, Theorem 3 part 1 (convergence of the myopic price path when N_g is empty); published as MSOM 27(5):1645-1663 (2025), doi:10.1287/msom.2024.0801

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.Myopic

open Filter Topology

/-- Theorem 3, part 1 (convergence half), p. 15. Under the standing assumptions `b > 0`,
`c⁺, c⁻ ≥ 0`, `α ∈ [0, 1]`, `p_H > 0` and the ceiling assumption `p_H ≥ p̂_H`, if no product is
gain-seeking (`c_i⁺ ≤ c_i⁻` for all `i`), then for every myopic policy `pm` and every initial
reference price `r⁰ ∈ Pⁿ` the myopic price path `t ↦ pm(r^t)` converges in `ℝⁿ`. -/
theorem theorem_3_convergence {n : ℕ} (a b cp cm : Fin n → ℝ) (α pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hpH : 0 < pH) (hceil : CeilingOK a b cp cm pH)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm)
    (hng : ∀ i, cp i ≤ cm i) (r₀ : Fin n → ℝ) (hr₀ : InBox pH r₀) :
    ∃ L : Fin n → ℝ, Tendsto (fun t => pm (myopicRef pm α r₀ t)) atTop (𝓝 L) := by sorry

end RefMNLPricing.Myopic
