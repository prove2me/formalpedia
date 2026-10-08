-- Prove2me | Theorems.Thm_ShapiroSDDP_Convergence_finite_cuts
-- name    : ShapiroSDDP.Convergence.finite_cuts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:20.267986+00:00
-- url     : https://prove2.me/theorems/12c634d0-7c86-4a55-84da-5967874bb03b
-- title:
--   §3.1, p. 10 — with basic optimal solutions, the number of cutting planes of the form (3.17) is finite
-- statement:
--   Fix a stage $1\le t\le T-1$ and a finite set $D$ of cuts of stage $t+1$ (the current $\mathfrak Q_{t+2}$). Then there is a finite set $F$ of affine functions of $x_t$, not depending on the trial point, with the following property: for every trial decision $\bar x\in\mathbb R^{n_t}$ and every choice, for each outcome $j=1,\dots,N_{t+1}$, of a basic optimal solution $(\pi_j,\rho_j)$ of the dual of the stage-$(t+1)$ problem
--   $$\min_{y,\theta}\ \tilde c_{t+1,j}^\top y+\theta\quad\text{s.t.}\quad \tilde A_{t+1,j}y=\tilde b_{t+1,j}-\tilde B_{t+1,j}\bar x,\ y\ge0,\ \theta\ge\alpha+\beta^\top y\ \ \forall(\alpha,\beta)\in D,$$
--   the cutting plane (3.17) built from these duals at $\bar x$,
--   $$\ell(x)=\underline{\widetilde{\mathcal Q}}_{t+1}(\bar x)+\tilde g^\top(x-\bar x),\qquad\tilde g=-\frac1{N_{t+1}}\sum_j\tilde B_{t+1,j}^\top\pi_j,$$
--   belongs to $F$.
--
--   It is the finiteness statement on which the finite convergence of the method rests.
--
--   **Formalization Note** The set $F$ is required not to depend on $\bar x$; the dual feasible regions do not depend on $\bar x$, only their objectives do. Finiteness is of cuts for a fixed next-stage cut set $D$, not of dual solutions overall, since the number of dual variables grows with $D$.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, p. 10, §3.1, after (3.17)

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model
import Definitions.Def_ShapiroSDDP_Convergence_SDDP

namespace ShapiroSDDP.Convergence

/-- §3.1, p. 10: when basic optimal dual solutions are used, only finitely many cutting planes
(3.17) can arise. For a stage `1 ≤ t ≤ T − 1` and a fixed cut set `D` of stage `t + 1` there is a
finite set `F` of cuts, not depending on the trial point, containing the cut (3.17) computed at
every trial point `x̄` from every choice of basic optimal dual solutions of the `N_{t+1}`
stage-`(t+1)` problems at `x̄` with the cut set `D`. -/
theorem finite_cuts (I : Instance) (t : ℕ) (ht : 1 ≤ t) (ht' : t + 1 ≤ I.T)
    (D : Finset (Cut I (t + 1))) :
    ∃ F : Finset (Cut I t), ∀ (x : Fin (I.n t) → ℝ)
      (d : Fin (I.N (t + 1)) → CutDual (I.m (t + 1)) D),
      (∀ j, IsBasicOptDual (I.A t j) (rhs I t x j) D (I.c t j) (d j)) →
        cutAt I t x D d ∈ F := by sorry

end ShapiroSDDP.Convergence
