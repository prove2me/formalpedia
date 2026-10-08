-- Prove2me | Theorems.Thm_StableFA_Discounted_corollary_3_1
-- name    : StableFA.Discounted.corollary_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:40:35.069352+00:00
-- url     : https://prove2.me/theorems/e0531067-3b00-4b28-b323-f7013439e94d
-- title:
--   Corollary 3.1, p. 6 — approximate value iteration with a nonexpansive M_F converges in max norm at the rate γ
-- statement:
--   Let $M$, $\gamma$, $T_M$ and $M_F$ be as in Theorem 3.1: a finite MDP on $n$ states with stochastic transition rows, discount $0\le\gamma<1$, its parallel value backup operator $T_M$, and a max-norm nonexpansion $M_F$ on $\mathbb R^n$. The approximate value iteration algorithm based on $F$ produces $V_{k+1}=M_F(T_M(V_k))$. There is a value function $V_\infty$ such that, from every initial guess $V_0$, the iterates converge to $V_\infty$ at the geometric rate $\gamma$:
--   $$\|(M_F\circ T_M)^k(V_0)-V_\infty\|\le\gamma^k\,\|V_0-V_\infty\|\qquad\text{for all }k\ge0,$$
--   and in particular $(M_F\circ T_M)^k(V_0)\to V_\infty$ as $k\to\infty$.
--
--   The corollary turns the contraction of Theorem 3.1 into a quantitative convergence statement for the algorithm actually run in practice.
--
--   **Formalization Note** "Converges at the rate $\gamma$" is read as the geometric rate of the Contraction Mapping theorem (Theorem 2.1, p. 2): the error after $k$ steps is at most $\gamma^k$ times the initial error, measured from the common limit $V_\infty$ (called `Vinf` in Lean). $\|\cdot\|$ on `Fin n → ℝ` is the max norm; $\gamma^0=1$, so the case $k=0$ is trivial.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 6, Corollary 3.1 (rate as in Theorem 2.1, p. 2)

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting

open Filter Topology

namespace StableFA.Discounted

theorem corollary_3_1 {n : ℕ} {C : Type} [Fintype C] (M : BertsekasSSPModel n C)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (MF : (Fin n → ℝ) → (Fin n → ℝ)) (hMF : ∀ Y Z : Fin n → ℝ, ‖MF Y - MF Z‖ ≤ ‖Y - Z‖) :
    ∃ Vinf : Fin n → ℝ,
      (∀ V : Fin n → ℝ,
        Tendsto (fun k => (MF ∘ BertsekasDiscountedBellmanOp M γ)^[k] V) atTop (𝓝 Vinf)) ∧
      ∀ (V : Fin n → ℝ) (k : ℕ),
        ‖(MF ∘ BertsekasDiscountedBellmanOp M γ)^[k] V - Vinf‖ ≤ γ ^ k * ‖V - Vinf‖ := by sorry

end StableFA.Discounted
