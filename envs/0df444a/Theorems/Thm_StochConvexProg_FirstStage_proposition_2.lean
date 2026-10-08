-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_proposition_2
-- name    : StochConvexProg.FirstStage.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:19.151907+00:00
-- url     : https://prove2.me/theorems/f6082a3c-cfa4-4f25-aa3b-1e5f426b9cd6
-- title:
--   Proposition 2 — F₂ is a normal convex integrand on S × Rⁿ¹ × Rⁿ² × R^{m₂}
-- statement:
--   Under the standing assumptions of the two-stage stochastic convex program, the second-stage integrand
--   $$(s,(x_1,x_2,u_2))\longmapsto F_2(s,x_1,x_2,u_2)$$
--   of (2.3) is a normal convex integrand on $S\times\mathbb R^{n_1}\times\mathbb R^{n_2}\times\mathbb R^{m_2}$.
--
--   Normality of $F_2$ is what makes the measurability and interchange results for integral functionals available for the recourse problem (Proposition 4, Theorems 1 and 2).
--
--   **Formalization Note** The integrand is $F_2$ uncurried on the product space $\mathbb R^{n_1}\times(\mathbb R^{n_2}\times\mathbb R^{m_2})$ with its Borel σ-algebra.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 182, Proposition 2

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_NormalIntegrand
import Definitions.Def_StochConvexProg_FirstStage_FirstStage

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Proposition 2, p. 182: `F₂` is a normal convex integrand on `S × Rⁿ¹ × Rⁿ² × R^{m₂}`. -/
theorem proposition_2 {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) :
    IsNormalConvexIntegrand
      (fun (s : S) (z : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) × (Fin m₂ → ℝ)) => pr.F₂ s z.1 z.2.1 z.2.2) := by sorry

end StochConvexProg.FirstStage
