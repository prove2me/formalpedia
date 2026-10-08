-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_theorem_4_2
-- name    : SSDConstraint.Optimality.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:09:15.890018+00:00
-- url     : https://prove2.me/theorems/88717e1c-47bd-4107-9127-d6540fcc7f42
-- title:
--   Theorem 4.2 — optimality conditions with a utility-function multiplier
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and consider the problem
--   $$\max f(X)\quad\text{subject to}\quad\mathbb E[(\eta-X)_+]\le\mathbb E[(\eta-Y)_+]\ \ \forall\eta\in[a,b],\qquad X\in C,\tag{3.1–3.3}$$
--   where $Y\in\mathcal L^1(\Omega,\mathcal F,P)$, $C\subseteq\mathcal L^1$ is convex and closed, and $f$ is concave and continuous on $C$. Let $L(X,u)=f(X)+\mathbb E[u(X)]-\mathbb E[u(Y)]$ (4.1), with $u$ in the class $\mathcal U_1$ of concave nondecreasing functions that vanish on $[b,\infty)$ and are affine with slope $c\ge0$ on $(-\infty,a]$. Assume the uniform dominance condition: some $\tilde X\in C$ has $\inf_{\eta\in[a,b]}\{F_2(Y;\eta)-F_2(\tilde X;\eta)\}>0$.
--
--   1. If $\hat X$ is an optimal solution of (3.1)–(3.3), there is $\hat u\in\mathcal U_1$ with
--   $$L(\hat X,\hat u)=\max_{X\in C}L(X,\hat u)\tag{4.2}$$
--   and
--   $$\mathbb E[\hat u(\hat X)]=\mathbb E[\hat u(Y)].\tag{4.3}$$
--   2. Conversely, if for some $\hat u\in\mathcal U_1$ a point $\hat X\in C$ maximizing $L(\cdot,\hat u)$ over $C$ satisfies (3.2) and (4.3), then $\hat X$ is an optimal solution of (3.1)–(3.3).
--
--   The theorem says that the Lagrange multiplier of a second-order stochastic dominance constraint can be taken to be a concave nondecreasing utility function: the optimal solution maximizes the objective plus the expected utility, for an implicit utility function determined by the problem.
--
--   **Formalization Note** $\mathcal U_1$ is formalized with $c\ge0$; the page prints $c>0$, under which part 1 is false (e.g. $Y\equiv0$, $[a,b]=[1,2]$, $f(X)=\mathbb E X$, $C$ the constants in $[0,1]$: $\hat X\equiv1$ is optimal and (4.3) forces $c=0$). "$=\max_{X\in C}$" is stated as membership in $C$ plus $L(X,\hat u)\le L(\hat X,\hat u)$ for all $X\in C$. The uniform dominance assumption is kept for both parts, as printed.
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 8, Theorem 4.2

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem
open MeasureTheory

namespace SSDConstraint.Optimality

/-- THEOREM 4.2, p. 8. Assume the uniform dominance condition. If `X̂` is an optimal solution of
(3.1)–(3.3), there is `û ∈ 𝒰₁` with `L(X̂, û) = max_{X ∈ C} L(X, û)` (4.2) and
`𝔼[û(X̂)] = 𝔼[û(Y)]` (4.3). Conversely, if for some `û ∈ 𝒰₁` a maximizer `X̂ ∈ C` of `L(·, û)` over
`C` satisfies (3.2) and (4.3), then `X̂` is an optimal solution of (3.1)–(3.3). -/
theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (pr : Problem Ω P) (hU : pr.UniformDominance) :
    (∀ Xh, pr.IsOptimal Xh → ∃ u ∈ U1 pr.a pr.b,
        (∀ X ∈ pr.C, pr.lagrangian X u ≤ pr.lagrangian Xh u) ∧
        ∫ ω, u (Xh ω) ∂P = ∫ ω, u (pr.Y ω) ∂P) ∧
    (∀ u ∈ U1 pr.a pr.b, ∀ Xh ∈ pr.C,
        (∀ X ∈ pr.C, pr.lagrangian X u ≤ pr.lagrangian Xh u) →
        (∀ η ∈ Set.Icc pr.a pr.b, ∫ ω, max (η - Xh ω) 0 ∂P ≤ ∫ ω, max (η - pr.Y ω) 0 ∂P) →
        ∫ ω, u (Xh ω) ∂P = ∫ ω, u (pr.Y ω) ∂P →
        pr.IsOptimal Xh) := by sorry

end SSDConstraint.Optimality
