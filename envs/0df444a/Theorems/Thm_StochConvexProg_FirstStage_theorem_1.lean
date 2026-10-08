-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_theorem_1
-- name    : StochConvexProg.FirstStage.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:25.109101+00:00
-- url     : https://prove2.me/theorems/fb5b7f57-a9fc-4c6b-bb57-25ae6f173e08
-- title:
--   Theorem 1 — if ρ(·, x₁) is essentially bounded for intrinsically feasible x₁, then j = J and inf Q = inf P
-- statement:
--   Suppose that for each $x_1$ which is intrinsically feasible in the first stage ($j(x_1)<+\infty$), the distance $\rho(s,x_1)$ from the origin to the set of feasible recourses is essentially bounded in $s$. Then
--   $$j(x_1)=\inf_{x_2\in\mathcal L^\infty_{n_2}}f(x_1,x_2)=J(x_1)\qquad\text{for all }x_1\in\mathbb R^{n_1}.$$
--   In particular $\inf\mathbf Q=\inf\mathbf P$, and $x_1$ gives the minimum in the intrinsic first-stage problem $\mathbf Q$ if and only if it gives the minimum in the first-stage problem induced by $\mathbf P$ (the minimization of $J$).
--
--   The theorem justifies restricting recourse functions to essentially bounded measurable ones: under its hypothesis nothing is lost by that restriction.
--
--   **Formalization Note** "Essentially bounded" is: there is a real $B$ with $\rho(s,x_1)\le B$ for almost every $s$ ($\rho\ge0$, so no lower bound is needed).
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 186, Theorem 1, (3.8)

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Theorem 1, p. 186: if `ρ(s, x₁)` is essentially bounded in `s` for each intrinsically feasible
`x₁`, then `j(x₁) = inf_{x₂ ∈ ℒ^∞_{n₂}} f(x₁, x₂)` for all `x₁` (3.8), `inf Q = inf P`, and `x₁` minimizes
`j` iff it minimizes `J`. -/
theorem theorem_1 {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (hρ : ∀ x₁, pr.IntrinsicallyFeasible x₁ → ∃ B : ℝ, ∀ᵐ s ∂σ, pr.ρ s x₁ ≤ (B : EReal)) :
    (∀ x₁, pr.j x₁ = pr.J x₁) ∧ pr.infQ = pr.infP ∧
      (∀ x₁, (∀ x₁', pr.j x₁ ≤ pr.j x₁') ↔ (∀ x₁', pr.J x₁ ≤ pr.J x₁')) := by sorry

end StochConvexProg.FirstStage
