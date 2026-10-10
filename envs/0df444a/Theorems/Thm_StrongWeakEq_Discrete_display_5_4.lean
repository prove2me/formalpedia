-- Prove2me | Theorems.Thm_StrongWeakEq_Discrete_display_5_4
-- name    : StrongWeakEq.Discrete.display_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:37.034626+00:00
-- url     : https://prove2.me/theorems/1d043a98-452a-454e-9d8d-bf7e6055ffeb
-- title:
--   (5.4), p. 15 — V(i, u ⊗₁ u*) = κ(0, i, uᵢ) + Σⱼ Hⱼ(u*) uᵢⱼ
-- statement:
--   Assume the standing assumptions of §5: $\mathcal A_i\subseteq\mathfrak P$ for every $i$, each $\kappa(t,i,\cdot)$ is continuous on $\mathfrak P$, and $\sum_t\sup_{(i,\alpha)\in S\times\mathfrak P}|\kappa(t,i,\alpha)|<\infty$ (5.2). Then for all $u,u^*\in\mathcal A$ and every initial state $i\in S$, the value of the concatenation $u\otimes_1u^*$ (row $u$ at time $0$, rows $u^*$ afterwards) decomposes as
--   $$V(i,u\otimes_1u^*)=\kappa(0,i,u_i)+\sum_{j=1}^N\mathbb E_{j,u^*}\Big[\sum_{t=0}^\infty\kappa(t+1,X_t,u^*_{X_t})\Big]\,u_{ij}=\kappa(0,i,u_i)+\sum_{j=1}^N H_j(u^*)\,u_{ij}.$$
--
--   The decomposition shows that $V(i,u\otimes_1u^*)$ depends on the deviation only through the row $u_i$, and is the sum of the time-$0$ payoff and an affine function of $u_i$. This is what makes the one-step deviation problem a finite-dimensional concave maximization in the existence proof.
--
--   **Formalization Note** $V(i,u\otimes_1u^*)$ is defined from the process: $\kappa(0,i,u_i)+\sum_{t\ge0}\sum_j(u(u^*)^t)_{ij}\kappa(t+1,j,u^*_j)$; $H_j(u^*)=\sum_{t\ge0}\sum_k((u^*)^t)_{jk}\kappa(t+1,k,u^*_k)$. Both are `tsum`s, so the content of the statement is the exchange of the infinite sum over $t$ with the finite sum over $j$, which (5.2) justifies. No summability is assumed. States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 15, (5.4)

import Mathlib
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel

namespace StrongWeakEq.Discrete

/-- (5.4), p. 15: `V(i, u ⊗₁ u*) = κ(0,i,uᵢ) + ∑ⱼ Hⱼ(u*) · u_{ij}`, where `V(i, u ⊗₁ u*)` is the value
of the chain driven by `u` at time `0` and by `u*` afterwards. -/
theorem display_5_4 {N : ℕ} {A : Fin N → Set (Fin N → ℝ)} {κ : ℕ → Fin N → (Fin N → ℝ) → ℝ}
    (hS : DStanding A κ) {u us : Matrix (Fin N) (Fin N) ℝ}
    (hu : u ∈ DControls A) (hus : us ∈ DControls A) (i : Fin N) :
    dConcatValue κ u us i = κ 0 i (u i) + ∑ j, dH κ us j * u i j := by sorry

end StrongWeakEq.Discrete
