-- Prove2me | Theorems.Thm_ShapiroSDDP_Convergence_attainment
-- name    : ShapiroSDDP.Convergence.attainment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:25.252587+00:00
-- url     : https://prove2.me/theorems/eea19edb-8110-496f-81b4-87436639b97b
-- title:
--   §3.1, p. 10 — a problem of the form (3.13)/(3.14) with finite optimal value has an optimal solution
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $h\in\mathbb R^m$, $c\in\mathbb R^n$, and let $C$ be a finite set of affine functions $y\mapsto\alpha+\beta^\top y$. Consider the linear program
--   $$\min_{y\in\mathbb R^n,\ \theta\in\mathbb R}\ c^\top y+\theta\quad\text{s.t.}\quad Ay=h,\ \ y\ge0,\ \ \theta\ge\alpha+\beta^\top y\ \text{ for all }(\alpha,\beta)\in C,$$
--   which is problem (3.13) or (3.14) written with the epigraph variable $\theta$ of the convex piecewise linear approximation $\mathfrak Q(y)=\max_{(\alpha,\beta)\in C}(\alpha+\beta^\top y)$. If this problem has a finite optimal value, that is, it is feasible and its objective is bounded below on the feasible set, then it has an optimal solution $(y^*,\theta^*)$.
--
--   This is the step that turns assumption (A1) into the existence of the forward decisions (3.13)–(3.14) used by the algorithm.
--
--   **Formalization Note** "Finite optimal value" is stated as feasibility plus a lower bound on the objective, not through an infimum.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, p. 10, §3.1, after (A1)

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model
import Definitions.Def_ShapiroSDDP_Convergence_SDDP

namespace ShapiroSDDP.Convergence

/-- §3.1, p. 10: a linear program of the form (3.13)/(3.14), i.e. minimize `cᵀ y + θ` subject to
`A y = h`, `y ≥ 0` and `θ ≥ α + βᵀ y` for each cut `(α, β)` of a finite set `C`, that has a finite
optimal value (feasible, objective bounded below) has an optimal solution. -/
theorem attainment {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ)
    (C : Finset (ℝ × (Fin n → ℝ))) (c : Fin n → ℝ) (hfin : CutLPFinite A h C c) :
    ∃ p, IsCutLPOpt A h C c p := by sorry

end ShapiroSDDP.Convergence
