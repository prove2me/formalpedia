-- Prove2me | Theorems.Thm_RobinsonSR_Reduction_proposition_A_2
-- name    : RobinsonSR.Reduction.proposition_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:21.704884+00:00
-- url     : https://prove2.me/theorems/fc3d5bfb-3979-49bf-9f7f-838b7fc47926
-- title:
--   Proposition A.2, p. 58 — on F = ∂ψ*_C(−y₀), ∂ψ_F(x) = ∂ψ_C(x) + y₀ℝ₊, and ∂ψ*_C(−y) ⊂ F for y near y₀
-- statement:
--   Let $C$ be a nonempty polyhedral convex set in $\mathbb R^n$, let $y_0\in\mathbb R^n$, and let $F:=\partial\psi_C^*(-y_0)$ be the face of $C$ on which $\langle -y_0,\cdot\rangle$ attains its maximum over $C$. Then:
--
--   1. for each $x\in F$,
--   $$\partial\psi_F(x)=\partial\psi_C(x)+y_0\mathbb R_+:=\{y+\alpha y_0 : y\in\partial\psi_C(x),\ \alpha\ge 0\};$$
--   2. for each $y$ sufficiently near $y_0$, $\partial\psi_C^*(-y)\subset F$.
--
--   Part 1 describes the normal cone of the exposed face $F$ in terms of that of $C$; part 2 says that small perturbations of the exposing vector can only select subfaces of $F$. Both are used in Proposition A.3 to localise a perturbed generalized equation on $C$ to the face $F$.
--
--   **Formalization Note** $\partial\psi_C^*(-y)$ is the set of maximisers of $\langle -y,\cdot\rangle$ over $C$, empty when the supremum is not attained; "for each $y$ near $y_0$" is an eventually-statement in the neighbourhood filter of $y_0$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 58, Proposition A.2

import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- Proposition A.2 (Robinson 1980, p. 58). Let `C` be a nonempty polyhedral convex set in `ℝⁿ`,
`y₀ ∈ ℝⁿ` and `F := ∂ψ*_C(-y₀)`. Then for each `x ∈ F`,
`∂ψ_F(x) = ∂ψ_C(x) + y₀ℝ₊ = {y + α y₀ | y ∈ ∂ψ_C(x), α ≥ 0}`; and for each `y` near `y₀`,
`∂ψ*_C(-y) ⊂ F`. -/
theorem proposition_A_2 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (y0 : EuclideanSpace ℝ (Fin n)) :
    (∀ x ∈ exposedFace C y0, normalCone (exposedFace C y0) x =
        {v | ∃ y ∈ normalCone C x, ∃ α : ℝ, 0 ≤ α ∧ v = y + α • y0}) ∧
    ∀ᶠ y in 𝓝 y0, exposedFace C y ⊆ exposedFace C y0 := by sorry

end RobinsonSR.Reduction
