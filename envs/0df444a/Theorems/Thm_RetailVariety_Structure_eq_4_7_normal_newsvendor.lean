-- Prove2me | Theorems.Thm_RetailVariety_Structure_eq_4_7_normal_newsvendor
-- name    : RetailVariety.Structure.eq_4_7_normal_newsvendor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:40.302126+00:00
-- url     : https://prove2.me/theorems/02e06f02-d77e-458c-8492-a35ef15edb03
-- title:
--   (4)–(7): under normal demand, $x^*_j=\lambda q_j+z\sigma(\lambda q_j)^\beta$ is optimal and the store profit is $\pi_I(S,v)$
-- statement:
--   Consider the independent population model. Let $v_j>0$ be the preferences of the variants and $v_0>0$ that of the no-purchase option, let $0<c<p$, $\lambda>0$, $\sigma>0$ and $0\le\beta<1$, let $z=\Phi^{-1}(1-c/p)$, and fix an assortment $S$ with MNL shares $q_j=q_j(S)$. For $j\in S$ the demand $Y_j$ is normal with mean $\lambda q_j$ and standard deviation $\sigma(\lambda q_j)^\beta$. Assume that every order-up-to level
--   $$x^*_j=\lambda q_j+z\sigma(\lambda q_j)^\beta,\qquad j\in S,$$
--   is nonnegative. Put $x^*_j=0$ for $j\notin S$. Then $x^*$ maximizes
--   $$\sum_{j\in S}E\bigl[p\min\{x_j,Y_j\}-cx_j\bigr]$$
--   over all stocking vectors $x\ge0$, and the maximum value is
--   $$\pi_I(S,v)=(p-c)\lambda\sum_{j\in S}q_j-\frac{p\sigma\lambda^\beta e^{-z^2/2}}{\sqrt{2\pi}}\sum_{j\in S}q_j^\beta .$$
--
--   This identifies the closed-form profit (7) with the stocking problem (4), so that the assortment problem can be posed on (7).
--
--   **Formalization Note** The nonnegativity of $x^*_j$ is the content of the paper's standing assumption $\lambda^{1-\beta}q_j\gg\sigma q_j^\beta$ (p. 1501); without it, the constraint $x\ge0$ binds when $z<0$ and (5) is not the optimum.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1502, §2.4.1, eqs. (4)–(7)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_RetailVariety_Structure_Newsvendor

open MeasureTheory ProbabilityTheory

namespace RetailVariety.Structure

/-- (4)–(7), p. 1502: in the independent population model, with `Y_j ~ N(λ q_j, (σ (λ q_j)^β)²)`
for `j ∈ S`, the stocking vector `x*_j = λ q_j + z σ (λ q_j)^β` (`j ∈ S`), `x*_j = 0` (`j ∉ S`)
maximizes `∑_{j∈S} E[p min{x_j, Y_j} - c x_j]` over `x ≥ 0`, and the maximum is `π_I(S, v)` of (7).
The hypothesis `x*_j ≥ 0` is the paper's `λ^{1-β} q_j ≫ σ q_j^β` (p. 1501). -/
theorem eq_4_7_normal_newsvendor {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (S : Finset (Fin n))
    (hx : ∀ j ∈ S, 0 ≤ lam * share v v0 S j
      + criticalFractile p c * σ * (lam * share v v0 S j) ^ β) :
    IsMaxOn
        (fun x : Fin n → ℝ => ∑ j ∈ S,
          newsvendorProfit (normalDemand lam σ β (share v v0 S j)) p c (x j))
        {x | ∀ j, 0 ≤ x j}
        (fun j => if j ∈ S then
          lam * share v v0 S j + criticalFractile p c * σ * (lam * share v v0 S j) ^ β else 0) ∧
      ∑ j ∈ S, newsvendorProfit (normalDemand lam σ β (share v v0 S j)) p c
          (lam * share v v0 S j + criticalFractile p c * σ * (lam * share v v0 S j) ^ β)
        = profitI p c lam σ β v v0 S := by sorry

end RetailVariety.Structure
