-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_sec_5_1_steady_state
-- name    : TwoSidedExp.DemandLimit.sec_5_1_steady_state
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:30.855672+00:00
-- url     : https://prove2.me/theorems/f0c2064b-50c8-4dd2-8c49-fba5f73890ae
-- title:
--   §5.1, p. 16 — every TSR design (aC, aL) ∈ [0,1]² has a unique mean-field steady state
-- statement:
--   Under the standing assumptions, let $a_C,a_L\in[0,1]$ and $\lambda,\tau>0$. Then the TSR experimental system with customer treatment fraction $a_C$ and listing treatment fraction $a_L$ has exactly one steady state $s^*(a_C,a_L)$: a unique vector $s=(s(\theta,j))$ with $0\le s(\theta,j)\le\rho(\theta,j)$ and
--   $$(\rho(\theta,j)-s(\theta,j))\,\tau\nu(\theta)=\lambda\sum_\gamma\sum_{i=0,1}\phi_{\gamma,i}\,p_{\gamma,i}(\theta,j\mid s)\qquad\text{for all }\theta,j.$$
--
--   This is what makes $s^*(a_C,a_L)$, and hence $Q_{ij}(\infty\mid a_C,a_L)$, well defined for every design, including the global designs $(1,1)$ and $(0,0)$ and the one-sided designs $(a_C,1)$ and $(1,a_L)$; in particular, the steady-state hypotheses of the mission's limit theorems can be met.
--
--   **Formalization Note** Only the steady-state part of the paper's claim is stated (existence and uniqueness of the solution of (45) in the state space), not the ODE statements. The closed square $[0,1]^2$ is used because Theorem 3 applies the claim at boundary designs; at such designs some types have mass $0$, so interiority is not claimed.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, §5.1, p. 16, after (16); (45), p. A6

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- §5.1, p. 16, after (16) (steady-state part): every TSR design `(aC, aL) ∈ [0,1]²` has, for every
`λ, τ > 0`, a unique steady state `s*(aC, aL)` of the experimental system, i.e. a unique solution
of (45) in its state space. -/
theorem sec_5_1_steady_state {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ)
    (hM : M.Standing) (aC aL : ℝ) (haC : aC ∈ Set.Icc (0 : ℝ) 1) (haL : aL ∈ Set.Icc (0 : ℝ) 1)
    (lam tau : ℝ) (hlam : 0 < lam) (htau : 0 < tau) :
    ∃! s : Θ × Fin 2 → ℝ, (M.expt aC aL).IsSteady lam tau s := by sorry

end TwoSidedExp.DemandLimit
