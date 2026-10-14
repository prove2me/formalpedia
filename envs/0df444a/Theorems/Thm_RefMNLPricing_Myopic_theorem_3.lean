-- Prove2me | Theorems.Thm_RefMNLPricing_Myopic_theorem_3
-- name    : RefMNLPricing.Myopic.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:15.553887+00:00
-- url     : https://prove2.me/theorems/566a2dad-cfcf-4132-b8b1-4b7748cb93ac
-- title:
--   Theorem 3, p. 15 — without gain-seeking products the myopic price path converges to a steady state; with one there is none
-- statement:
--   Consider the MNL pricing model with reference effects: products $i\in N$ with $a_i\in\mathbb R$, $b_i>0$, $c_i^+,c_i^-\ge0$, memory $\alpha\in[0,1]$, price box $\mathcal P^n=[0,p_H]^n$ with $p_H>0$, and the ceiling assumption $p_H\ge\hat p_H$. Let $p^m$ be any myopic pricing policy (for each $r\in\mathcal P^n$, $p^m(r)$ maximises $\Pi(\cdot,r)$ over $\mathcal P^n$), and for an initial reference price $r^0\in\mathcal P^n$ let
--
--   $$
--   r^{t+1} = \alpha r^t + (1-\alpha)\,p^m(r^t),\qquad t\ge0 .
--   $$
--
--   A policy has a **steady state** if $p^m(r) = r$ for some $r\in\mathcal P^n$.
--
--   1. If no product is gain-seeking ($c_i^+\le c_i^-$ for all $i$, i.e. $N_g=\emptyset$), then for every $r^0\in\mathcal P^n$ the myopic price path $\{p^m(r^t)\}_{t\ge0}$ converges to some $L\in\mathcal P^n$, and if $\alpha<1$ the limit is a steady state: $p^m(L)=L$.
--   2. If some product is gain-seeking ($c_i^+>c_i^-$ for some $i$, i.e. $N_g\neq\emptyset$), then $p^m$ has no steady state: $p^m(r)\neq r$ for every $r\in\mathcal P^n$. Moreover, if $\alpha<1$, the myopic price path from any $r^0\in\mathcal P^n$ does not converge.
--
--   The dichotomy says that gain-seeking consumers are exactly what makes myopic pricing oscillate: with only loss-averse and loss-neutral products the myopic price path settles (at a limit that may depend on $r^0$), whereas a single gain-seeking product rules out any steady state.
--
--   **Formalization Note** Both parts hold for every myopic policy, i.e. every selection of maximisers. In part 1 convergence is claimed for every $\alpha\in[0,1]$, but the fixed-point property of the limit needs $\alpha<1$: at $\alpha=1$ the reference price never moves and the path is the constant $p^m(r^0)$, which is generally not a fixed point. In part 2 the paper's "admits no steady state" is formalized literally (no $r\in\mathcal P^n$ with $p^m(r)=r$); the non-convergence clause for $\alpha<1$ is an addition, the contrapositive of the paper's remark on p. 15 that a convergent price path forces a steady state, and is false at $\alpha=1$. Convergence is in the product topology on $\mathbb R^n$.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 15, Theorem 3; steady-state definition §3.2, p. 15; standing assumption §2.4, p. 11

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.Myopic

open Filter Topology

/-- Theorem 3, p. 15. Under the standing assumptions `b > 0`, `c⁺, c⁻ ≥ 0`, `α ∈ [0, 1]`, `p_H > 0`
and the ceiling assumption `p_H ≥ p̂_H`, for every myopic policy `pm`:
1. if no product is gain-seeking (`c_i⁺ ≤ c_i⁻` for all `i`), then from every initial reference
   price `r⁰ ∈ Pⁿ` the myopic price path `t ↦ pm(r^t)` converges to some `L ∈ Pⁿ`, and when
   `α < 1` the limit is a steady state, `pm L = L`;
2. if some product is gain-seeking (`c_i⁻ < c_i⁺`), then `pm` has no steady state in `Pⁿ`
   (`pm r ≠ r` for every `r ∈ Pⁿ`), and when `α < 1` the myopic price path from every `r⁰ ∈ Pⁿ`
   does not converge. -/
theorem theorem_3 {n : ℕ} (a b cp cm : Fin n → ℝ) (α pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hpH : 0 < pH) (hceil : CeilingOK a b cp cm pH)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm) :
    ((∀ i, cp i ≤ cm i) →
      ∀ r₀ : Fin n → ℝ, InBox pH r₀ →
        ∃ L : Fin n → ℝ, InBox pH L ∧
          Tendsto (fun t => pm (myopicRef pm α r₀ t)) atTop (𝓝 L) ∧
          (α < 1 → pm L = L)) ∧
    ((∃ i, cm i < cp i) →
      (∀ r : Fin n → ℝ, InBox pH r → pm r ≠ r) ∧
      (α < 1 → ∀ r₀ : Fin n → ℝ, InBox pH r₀ →
        ¬ ∃ L : Fin n → ℝ, Tendsto (fun t => pm (myopicRef pm α r₀ t)) atTop (𝓝 L))) := by sorry

end RefMNLPricing.Myopic
