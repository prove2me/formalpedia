-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_eq_3_5_3_6
-- name    : StochConvexProg.FirstStage.eq_3_5_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:22.736103+00:00
-- url     : https://prove2.me/theorems/91d8c1fd-7878-4d6f-9d3f-a5a4eba891ba
-- title:
--   (3.5)–(3.6) — j(x₁) ≤ f(x₁, x₂) for all x₁, x₂, hence inf Q ≤ inf P
-- statement:
--   For the intrinsic first-stage objective $j$ and the essential objective $f$ of $\mathbf P$,
--   $$j(x_1)\le f(x_1,x_2)\qquad\text{for all } x_1\in\mathbb R^{n_1},\ x_2\in\mathcal L^\infty_{n_2},$$
--   and therefore
--   $$\inf\mathbf Q\le\inf\mathbf P.$$
--
--   This is the easy half of the comparison between the intrinsic first-stage problem and $\mathbf P$; Theorems 1 and 2 give conditions for equality.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 186, (3.5)–(3.6)

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- (3.5)–(3.6), p. 186: `j(x₁) ≤ f(x₁, x₂)` for all `x₁ ∈ Rⁿ¹`, `x₂ ∈ ℒ^∞_{n₂}`, and therefore
`inf Q ≤ inf P`. -/
theorem eq_3_5_3_6 {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) :
    (∀ (x₁ : Fin n₁ → ℝ) (x₂ : Lp (Fin n₂ → ℝ) ⊤ σ), pr.j x₁ ≤ pr.f (x₁, x₂)) ∧
      pr.infQ ≤ pr.infP := by sorry

end StochConvexProg.FirstStage
