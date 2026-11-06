-- Prove2me | Theorems.Thm_TimeInconsLQ_Sufficient_state_unique
-- name    : TimeInconsLQ.Sufficient.state_unique
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T14:08:49.890091+00:00
-- url     : https://prove2.me/theorems/eeab7f0f-2a73-408e-ad0a-2a8fb8a6ff9f
-- title:
--   §2, p. 3 — the state equation (2.1) has a unique solution (uniqueness part)
-- statement:
--   Uniqueness of the state process of the time-inconsistent stochastic LQ problem.
--
--   Work under the standing assumptions of §2: $W=(W^1,\dots,W^d)$ is a standard $d$-dimensional Brownian motion on $(\Omega,\mathcal F,P)$ with its natural filtration $(\mathcal F_t)$, $A$ is a bounded deterministic $n\times n$ matrix function on $[0,T]$, the coefficients $B,C^j,D^j$ are essentially bounded progressively measurable processes, and $b,\sigma^j\in L^2_{\mathcal F}(0,T;\mathbb R^n)$. Fix an admissible control $u\in L^2_{\mathcal F}(0,T;\mathbb R^l)$. If $X$ and $X'$ are both solutions of the state equation
--
--   $$
--   dX_s=[A_sX_s+B_s'u_s+b_s]\,ds+\sum_{j=1}^d[C^j_sX_s+D^j_su_s+\sigma^j_s]\,dW^j_s,\qquad X_0=x_0,\qquad s\in[0,T],
--   $$
--
--   then for every $s\in[0,T]$,
--
--   $$
--   X_s=X'_s\quad P\text{-almost surely}.
--   $$
--
--   This is the uniqueness half of the paper's remark (p. 3) that for every control $u\in L^2_{\mathcal F}(0,T;\mathbb R^l)$ the state equation (2.1) has a unique solution. It allows statements proved along one state process of $u^*$ (such as the expansion of Proposition 3.1) to be transferred to any other state process of the same control.
--
--   **Formalization Note** A solution of (2.1) is the model's `IsState`: a progressively measurable process with $\sup_{t\le T}E|X_t|^2<\infty$ satisfying the integral form of (2.1) almost surely at every time $t\in[0,T]$, with the stochastic integrals being $L^2$ Itô integrals in the sense of `Peng1990.SMP.IsItoIntegral`.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, §2, p. 3 (after (2.1): "there exists a unique solution X")

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model

namespace TimeInconsLQ.Sufficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- §2, p. 3 (uniqueness part of "for any control `u ∈ L²_𝓕(0, T; ℝˡ)` there exists a unique
solution `X`" of the state equation (2.1)): under the standing assumptions, any two state
processes `X`, `X'` of the same admissible control `u` agree almost surely at every time
`s ∈ [0, T]`. -/
theorem state_unique {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ} (M : Data Ω n l d)
    (hM : Standing M) (u : ℝ≥0 → Ω → Fin l → ℝ) (hu : Admissible M u)
    (X X' : ℝ≥0 → Ω → Fin n → ℝ) (hX : IsState M u X) (hX' : IsState M u X') :
    ∀ s : ℝ≥0, s ≤ M.T → X s =ᵐ[M.P] X' s := by sorry

end TimeInconsLQ.Sufficient
