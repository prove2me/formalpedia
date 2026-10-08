-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_theorem_2
-- name    : StochConvexProg.FirstStage.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:12.741391+00:00
-- url     : https://prove2.me/theorems/c81ca1cf-7104-4322-9fcf-f4723d5c95a0
-- title:
--   Theorem 2 — with C₂ bounded, j = J, inf Q = inf P, the same first-stage minimizers, and the infimum over ℒ^∞ recourses is attained
-- statement:
--   Consider the two-stage stochastic convex program under its standing assumptions, and suppose the second-stage constraint set $C_2$ is bounded. Then the conclusions of Theorem 1 hold:
--
--   1. $j(x_1)=J(x_1)=\inf_{x_2\in\mathcal L^\infty_{n_2}}f(x_1,x_2)$ for every $x_1\in\mathbb R^{n_1}$ (3.8);
--   2. $\inf\mathbf Q=\inf\mathbf P$;
--   3. $x_1$ gives the minimum in the intrinsic first-stage problem $\mathbf Q$ if and only if it gives the minimum in the first-stage problem induced by $\mathbf P$;
--
--   and moreover
--
--   4. for each $x_1\in\mathbb R^{n_1}$ the infimum in (3.8) is attained: there is $x_2\in\mathcal L^\infty_{n_2}$ with
--   $$f(x_1,x_2)=\inf_{x_2'\in\mathcal L^\infty_{n_2}}f(x_1,x_2').$$
--
--   Thus when $C_2$ is bounded, restricting recourse to essentially bounded measurable functions loses no generality, and an optimal recourse function exists for every first-stage decision.
--
--   **Formalization Note** "Gives the minimum" is "$\le$ the value at every other point". $J(x_1)$ is the `EReal` infimum over all of $\mathcal L^\infty_{n_2}$ (`Lp (Fin n₂ → ℝ) ⊤ σ`).
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 187, Theorem 2 (with Theorem 1, p. 186)

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Theorem 2, p. 187: if `C₂` is bounded, the conclusions of Theorem 1 hold (`j = J`, `inf Q = inf P`,
the same first-stage minimizers), and the infimum in (3.8) is attained for each `x₁` by some
`x₂ ∈ ℒ^∞_{n₂}`. -/
theorem theorem_2 {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (hC₂ : Bornology.IsBounded pr.C₂) :
    (∀ x₁, pr.j x₁ = pr.J x₁) ∧ pr.infQ = pr.infP ∧
      (∀ x₁, (∀ x₁', pr.j x₁ ≤ pr.j x₁') ↔ (∀ x₁', pr.J x₁ ≤ pr.J x₁')) ∧
      (∀ x₁, ∃ x₂ : Lp (Fin n₂ → ℝ) ⊤ σ, pr.f (x₁, x₂) = pr.J x₁) := by sorry

end StochConvexProg.FirstStage
