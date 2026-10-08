-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_proposition_4
-- name    : StochConvexProg.FirstStage.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:37.252323+00:00
-- url     : https://prove2.me/theorems/e6558861-f0ef-4945-bc03-fa3029bb276f
-- title:
--   Proposition 4 — the optimal recourse cost q(s, x₁) is measurable in s
-- statement:
--   For each $x_1\in\mathbb R^{n_1}$, the optimal recourse cost
--   $$q(s,x_1)=\inf_{x_2\in\mathbb R^{n_2}}F_2(s,x_1,x_2,0)\in[-\infty,+\infty]$$
--   is a measurable function of $s\in S$.
--
--   This is the measurability needed for the integral in the definition of the intrinsic first-stage objective $j(x_1)=F_1(x_1,0)+\int_S q(s,x_1)\,\sigma(ds)$ to be meaningful.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 185, Proposition 4

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Proposition 4, p. 185: for each `x₁ ∈ Rⁿ¹`, `q(s, x₁)` is measurable in `s ∈ S`. -/
theorem proposition_4 {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) :
    ∀ x₁ : Fin n₁ → ℝ, Measurable (fun s => pr.q s x₁) := by sorry

end StochConvexProg.FirstStage
