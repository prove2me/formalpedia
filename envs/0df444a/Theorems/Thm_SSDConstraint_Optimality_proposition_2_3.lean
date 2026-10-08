-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_proposition_2_3
-- name    : SSDConstraint.Optimality.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:08:53.146969+00:00
-- url     : https://prove2.me/theorems/9ac2df1f-e815-4195-88b8-5a94f0aefd3b
-- title:
--   Proposition 2.3 — $A_2(Y)$ is convex and closed; its recession cone is $\{H\ge0\text{ a.s.}\}$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $Y\in\mathcal L^1(\Omega,\mathcal F,P)$. Let
--   $$A_2(Y)=\{X\in\mathcal L^1(\Omega,\mathcal F,P): F_2(X;\eta)\le F_2(Y;\eta)\ \text{for all }\eta\in\mathbb R\}$$
--   be the set of outcomes dominating $Y$ in the second order. The recession cone of a convex set $A$ is $A^\infty=\{H: A+\tau H\subseteq A\text{ for all }\tau\ge0\}$. Then $A_2(Y)$ is convex and closed in $\mathcal L^1$, and
--   $$A_2^\infty(Y)=\{H\in\mathcal L^1(\Omega,\mathcal F,P): H\ge0\text{ a.s.}\}.$$
--
--   The convexity of $A_2(Y)$ is the convexity of the dominance constraint, which makes problem (3.1)–(3.3) a convex program.
--
--   **Formalization Note** $\mathcal L^1$ is Mathlib's space of a.e.-classes `Ω →₁[P] ℝ` with its norm topology; $F_2$ is the published `DualSSD.Shared.secondPerformance`.
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 5, Proposition 2.3 (with the definition of A_2(Y) and of the recession cone just before it)

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem
open MeasureTheory

namespace SSDConstraint.Optimality

/-- PROPOSITION 2.3, p. 5: for every `Y ∈ L¹(Ω, ℱ, P)` the set `A₂(Y)` is convex and closed, and its
recession cone `{H : A₂(Y) + τH ⊆ A₂(Y) for all τ ≥ 0}` is `{H ∈ L¹ : H ≥ 0 a.s.}`. -/
theorem proposition_2_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω →₁[P] ℝ) :
    Convex ℝ (A2 P Y) ∧ IsClosed (A2 P Y) ∧
      {H : Ω →₁[P] ℝ | ∀ X ∈ A2 P Y, ∀ τ : ℝ, 0 ≤ τ → X + τ • H ∈ A2 P Y} =
        {H : Ω →₁[P] ℝ | 0 ≤ᵐ[P] ⇑H} := by sorry

end SSDConstraint.Optimality
