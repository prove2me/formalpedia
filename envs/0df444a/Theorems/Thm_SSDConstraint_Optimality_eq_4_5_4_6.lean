-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_eq_4_5_4_6
-- name    : SSDConstraint.Optimality.eq_4_5_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:31:37.672992+00:00
-- url     : https://prove2.me/theorems/7b55c72a-fb52-4833-86ba-9a025b726df0
-- title:
--   Proof of Theorem 4.2, (4.5)–(4.6) — a nonnegative measure multiplier exists
-- statement:
--   Consider problem (3.1)–(3.3) with data $Y$, $C$ (convex, closed), $f$ (concave, continuous on $C$) and $[a,b]$, and assume the uniform dominance condition (Definition 4.1). Let $\hat X$ be an optimal solution. Then there exists a nonnegative measure $\hat\mu\in\mathbf{rca}([a,b])$ such that
--   $$\Lambda(\hat X,\hat\mu)=\max_{X\in C}\Lambda(X,\hat\mu)\tag{4.5}$$
--   and
--   $$\int_a^b\big[F_2(Y;\eta)-F_2(\hat X;\eta)\big]\,d\hat\mu(\eta)=0,\tag{4.6}$$
--   where $\Lambda(X,\mu)=f(X)+\int_a^b[F_2(Y;\eta)-F_2(X;\eta)]\,d\mu(\eta)$ is the Lagrangian (4.4).
--
--   This is the existence of a Lagrange multiplier for the dominance constraint viewed as a cone constraint in $\mathcal C([a,b])$, before it is translated into a utility function.
--
--   **Formalization Note** A nonnegative measure in $\mathbf{rca}([a,b])$ is represented, as the page does, by its extension to $\mathbb R$ assigning mass $0$ off $[a,b]$: a finite Borel measure $\mu$ on $\mathbb R$ with $\mu(\mathbb R\setminus[a,b])=0$ (every finite Borel measure on $\mathbb R$ is regular). "$=\max_{X\in C}$" is stated as $\Lambda(X,\hat\mu)\le\Lambda(\hat X,\hat\mu)$ for all $X\in C$; $\hat X\in C$ follows from optimality.
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), pp. 8–9, proof of Theorem 4.2, (4.4)–(4.6)

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Multiplier
open MeasureTheory

namespace SSDConstraint.Optimality

/-- Proof of Theorem 4.2, (4.4)–(4.6), pp. 8–9: under the uniform dominance condition, for every optimal
solution `X̂` of (3.1)–(3.3) there is a nonnegative measure `μ̂ ∈ rca([a, b])` (a finite Borel measure
on `ℝ` vanishing off `[a, b]`) with `Λ(X̂, μ̂) = max_{X ∈ C} Λ(X, μ̂)` (4.5) and
`∫_a^b [F₂(Y; η) − F₂(X̂; η)] dμ̂(η) = 0` (4.6). -/
theorem eq_4_5_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (pr : Problem Ω P) (hU : pr.UniformDominance) (Xh : Ω →₁[P] ℝ) (hXh : pr.IsOptimal Xh) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Set.Icc pr.a pr.b)ᶜ = 0 ∧
      (∀ X ∈ pr.C, pr.Lambda X μ ≤ pr.Lambda Xh μ) ∧
      ∫ η in Set.Icc pr.a pr.b, (F2 P pr.Y η - F2 P Xh η) ∂μ = 0 := by sorry

end SSDConstraint.Optimality
