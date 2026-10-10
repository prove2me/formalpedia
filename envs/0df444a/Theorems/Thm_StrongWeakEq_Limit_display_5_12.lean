-- Prove2me | Theorems.Thm_StrongWeakEq_Limit_display_5_12
-- name    : StrongWeakEq.Limit.display_5_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:19.617127+00:00
-- url     : https://prove2.me/theorems/9d72a522-d4f4-4486-8416-61bb838331e8
-- title:
--   (5.12), p. 17 — an equilibrium uⁿ of the discretized problem satisfies κⁿ(0,i,uⁿᵢ) + Hⁿ(uⁿ)·uⁿᵢ ≥ κⁿ(0,i,uᵢ) + Hⁿ(uⁿ)·uᵢ
-- statement:
--   Consider the continuous-time model of §2 under its standing assumptions (2.1)–(2.3) and the eventual monotonicity (5.8). Fix a mesh $\delta_n>0$ and the discretized problem $V^n$ with payoff $\kappa^n$ of (5.9) and admissible transition matrices $\mathcal A^n$ of (5.11). Let $u^n\in\mathcal A^n$ be an equilibrium of $V^n$ (Definition 5.1), i.e. $V^n(i,u^n)\ge V^n(i,u\otimes_1u^n)$ for all $i\in S$ and $u\in\mathcal A^n$, and let
--
--   $$
--   H^n_i(u^n)=\mathbb E_{i,u^n}\Big[\sum_{k=0}^\infty\kappa^n(k+1,X_k,u^n_{X_k})\Big],\qquad i\in S. \qquad (5.13)
--   $$
--
--   Then for every $i\in S$ and $u\in\mathcal A^n$,
--
--   $$
--   \kappa^n(0,i,u^n_i)+H^n(u^n)\cdot u^n_i\ \ge\ \kappa^n(0,i,u_i)+H^n(u^n)\cdot u_i. \qquad (5.12)
--   $$
--
--   This one-step inequality is the discrete first-order condition that the proof of Theorem 5.2 passes to the limit; it rewrites the equilibrium property through the decomposition of $V^n$ into the immediate payoff and the continuation values $H^n$.
--
--   **Formalization Note** $H^n(u^n)\cdot u_i$ is the dot product $\sum_jH^n_j(u^n)u_{ij}$. The sums defining $V^n$, $H^n$ and $V^n(i,u\otimes_1u^n)$ are `tsum`s; their summability is not assumed but follows from (2.3) and (5.8) (the generator rows of matrices in $\mathcal A^n$ are bounded by $2/\delta_n$, and by (5.8) the tail of the series is dominated by the integral of the majorant of (2.3)). The paper does not state (5.2) for $\kappa^n$, and it is not assumed. States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 17, (5.12)–(5.13)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel
import Definitions.Def_StrongWeakEq_Limit_Discretization

namespace StrongWeakEq.Limit

/-- (5.12), p. 17: under (2.1)–(2.3) and (5.8), an equilibrium `uⁿ ∈ 𝒜ⁿ` of the discretized problem
with mesh `δ > 0` satisfies, for all `i` and `u ∈ 𝒜ⁿ`,
`κⁿ(0,i,uⁿᵢ) + Hⁿ(uⁿ)·uⁿᵢ ≥ κⁿ(0,i,uᵢ) + Hⁿ(uⁿ)·uᵢ`. -/
theorem display_5_12 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : StrongWeakEq.Existence.Standing D f)
    (h58 : EventuallyNonincreasing D f) (δ : ℝ) (hδ : 0 < δ)
    (un : Matrix (Fin N) (Fin N) ℝ)
    (heq : StrongWeakEq.Discrete.IsDEquilibrium (admRows D δ) (kappaN f δ) un) :
    ∀ i, ∀ u ∈ StrongWeakEq.Discrete.DControls (admRows D δ),
      kappaN f δ 0 i (u i) + (fun j => StrongWeakEq.Discrete.dH (kappaN f δ) un j) ⬝ᵥ u i ≤
        kappaN f δ 0 i (un i) + (fun j => StrongWeakEq.Discrete.dH (kappaN f δ) un j) ⬝ᵥ un i := by sorry

end StrongWeakEq.Limit
