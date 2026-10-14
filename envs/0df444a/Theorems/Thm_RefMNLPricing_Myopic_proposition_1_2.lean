-- Prove2me | Theorems.Thm_RefMNLPricing_Myopic_proposition_1_2
-- name    : RefMNLPricing.Myopic.proposition_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:05.455007+00:00
-- url     : https://prove2.me/theorems/0f910944-dfa8-480e-98bc-a056ed11b609
-- title:
--   Proposition 1.2, p. 10 — (9) has a unique root p̂_H, and for p_H ≥ p̂_H the ceiling does not bind the myopic problem
-- statement:
--   Consider the MNL pricing model with $n$ products, parameters $a_i\in\mathbb R$, $b_i>0$, $c_i^+, c_i^-\ge 0$, revenue $\Pi(p,r)$ and price box $\mathcal P^n = [0,p_H]^n$ with $p_H>0$. Let $\chi := \max_{i} 1/(b_i+\min\{c_i^+,c_i^-\})$.
--
--   1. The equation
--   $$
--   p = \chi + \sum_{i\in N} \frac{1}{b_i+c_i^+}\exp\big(a_i - b_i p + (b_i+c_i^+)\chi - 1\big) \qquad (9)
--   $$
--   has exactly one real solution $p = \hat p_H$.
--
--   2. If $p_H \ge \hat p_H$, then for every reference price $r\in\mathcal P^n$ the maximisers of $\Pi(\cdot,r)$ over the box coincide with its maximisers over all of $\mathbb R^n$:
--   $$
--   \operatorname*{arg\,max}_{p\in\mathcal P^n} \Pi(p,r) = \operatorname*{arg\,max}_{p\in\mathbb R^n} \Pi(p,r).
--   $$
--
--   This is what makes the ceiling assumption $p_H\ge\hat p_H$, used throughout the analysis of the myopic policy, a non-binding constraint: the myopic problem is effectively unconstrained.
--
--   **Formalization Note** The set equality (10) is stated pointwise: for every $p\in\mathbb R^n$, $p$ is a maximiser over the box iff $\Pi(p',r)\le\Pi(p,r)$ for every $p'\in\mathbb R^n$. "$p_H\ge\hat p_H$" is stated for the solution $\hat p_H$ of (9) given by hypothesis. $\chi$ is $0$ when $n=0$.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 10, Proposition 1.2, (9)–(10)

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.Myopic

/-- Proposition 1.2, p. 10. Equation (9), `p = ceilRHS p`, has a unique solution `p̂_H`, and for
every ceiling `p_H ≥ p̂_H` and every reference price `r ∈ Pⁿ` the maximisers of `Π(·, r)` over the
box `Pⁿ = [0, p_H]ⁿ` are exactly the maximisers of `Π(·, r)` over all of `ℝⁿ` (the set equality
(10)). -/
theorem proposition_1_2 {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH) :
    (∃! p : ℝ, p = ceilRHS a b cp cm p) ∧
    ∀ pHat : ℝ, pHat = ceilRHS a b cp cm pHat → pHat ≤ pH →
      ∀ r : Fin n → ℝ, InBox pH r → ∀ p : Fin n → ℝ,
        (IsBoxMax a b cp cm pH r p ↔
          ∀ p' : Fin n → ℝ, revenue a b cp cm p' r ≤ revenue a b cp cm p r) := by sorry

end RefMNLPricing.Myopic
