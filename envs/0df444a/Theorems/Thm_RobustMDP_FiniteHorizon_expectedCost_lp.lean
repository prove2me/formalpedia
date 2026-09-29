-- Prove2me | Theorems.Thm_RobustMDP_FiniteHorizon_expectedCost_lp
-- name    : RobustMDP.FiniteHorizon.expectedCost_lp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:20:25.927837+00:00
-- url     : https://prove2.me/theorems/118b8d93-8b64-4c16-8477-ac3793bb6089
-- title:
--   Eq. (14), p. 783 — the expected cost of a fixed policy is the value of a linear program
-- statement:
--   Fix an initial state $i_0$, a controller policy $\pi=(\mathbf a_t)_{t\in T}$ and transition matrices $P=(P_t^a)_{a\in\mathcal A,\,t\in T}$ whose rows are probability vectors. Let $q=e_{i_0}$ ($q(i_0)=1$, $q(i)=0$ otherwise). Then the expected total cost $C_N(\pi,P)$ of (2) is the optimal value of the linear program
--
--   $$
--   \max_{v_0,\dots,v_{N-1}}\ q^{\mathsf T}v_0\quad\text{s.t.}\quad v_t(i)\le c_t(i,\mathbf a_t(i))+\sum_j P_t^{\mathbf a_t(i)}(i,j)\,v_{t+1}(j),\quad i\in\mathcal X,\ t\in T, \tag{14}
--   $$
--
--   with $v_N=c_N$, and the maximum is attained.
--
--   The linear program links the probabilistic definition (2) of the cost to the backward recursions: letting the matrices vary over nature's admissible set turns (14) into problem (16).
--
--   **Formalization Note** The cost $C_N$ is the forward-distribution expectation of (2). The terminal condition $v_N=c_N$ is implicit on the page (the paper writes $\varphi_N(\pi,\tau)$ for $C_N(\pi,\tau)$ here). Since $q=e_{i_0}$, the objective $q^{\mathsf T}v_0$ is written $v_0(i_0)$. The maximum is stated with `IsGreatest`.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 783, Eq. (14)

import Mathlib
import Definitions.Def_RobustMDP_FiniteHorizon_Model
import Definitions.Def_RobustMDP_FiniteHorizon_expectedCost

namespace RobustMDP.FiniteHorizon

/-- The linear program (14), p. 783. For a given controller policy `π` and a given collection of
time-varying transition matrices `P = (P_t^a)` (every row a probability vector), the expected
total cost `C_N(π, P)` of (2) is the optimal value of
`max qᵀ v_0` over `v_0, …, v_{N-1}` subject to
`v_t(i) ≤ c_t(i, 𝐚_t(i)) + ∑_j P_t^{𝐚_t(i)}(i, j) v_{t+1}(j)` for all `i`, `t ∈ T`, with
`v_N = c_N` and `q = e_{i₀}` (so `qᵀ v_0 = v_0(i₀)`). -/
theorem expectedCost_lp {n N : ℕ} {A : Type} (M : Model n N A) (i₀ : Fin n)
    (π : ControlPolicy n N A) (P : Fin N → A → Fin n → Fin n → ℝ)
    (hP : ∀ t a i, P t a i ∈ stdSimplex ℝ (Fin n)) :
    IsGreatest
      {x : ℝ | ∃ v : Fin (N + 1) → Fin n → ℝ,
        v (Fin.last N) = M.terminalCost ∧
        (∀ t : Fin N, ∀ i, v t.castSucc i ≤
          M.cost t i (π t i) + ∑ j, P t (π t i) i j * v t.succ j) ∧
        x = v 0 i₀}
      (M.expectedCost i₀ π P) := by sorry

end RobustMDP.FiniteHorizon
