-- Prove2me | Theorems.Thm_StochConvexProg_Duality_summable_of_bounded
-- name    : StochConvexProg.Duality.summable_of_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:08.547743+00:00
-- url     : https://prove2.me/theorems/c6bed49b-b32f-4e90-ba41-13c18f7a53f5
-- title:
--   p. 174 — s ↦ f₂ᵢ(s, x₁(s), x₂(s)) is measurable, summable for i = 0 and essentially bounded for i ≥ 1
-- statement:
--   Let the data satisfy the standing assumptions of the model, with $\sigma$ a probability measure. Let $x_1:S\to\mathbb R^{n_1}$ and $x_2:S\to\mathbb R^{n_2}$ be bounded measurable functions. Then the functions
--   $$s\mapsto f_{2i}(s,x_1(s),x_2(s)),\qquad i=0,1,\dots,m_2,$$
--   are measurable; the one with $i=0$ is summable (integrable), and those with $i=1,\dots,m_2$ are essentially bounded.
--
--   In particular the expected cost $f_{10}(x_1)+\int_S f_{20}(s,x_1,x_2(s))\,\sigma(ds)$ is a well-defined real number whenever $x_2$ is bounded and measurable, which is what makes the perturbation functional $F$ meaningful on $X\times U$.
--
--   **Formalization Note** Boundedness of $x_1,x_2$ is with respect to the sup norm of `Fin n → ℝ`; boundedness does not depend on the norm. Essential boundedness is an almost-everywhere bound.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 174, the sentence after the standing assumptions

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem

open MeasureTheory

namespace StochConvexProg.Duality

/-- Rockafellar–Wets (1976), p. 174: for bounded measurable `x₁ : S → Rⁿ¹`, `x₂ : S → Rⁿ²` the
functions `s ↦ f₂ᵢ(s, x₁(s), x₂(s))` are measurable, summable for `i = 0` and essentially bounded
for `i = 1, …, m₂`. -/
theorem summable_of_bounded {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (x₁ : S → Fin n₁ → ℝ) (x₂ : S → Fin n₂ → ℝ)
    (hx₁ : Measurable x₁) (hx₂ : Measurable x₂)
    (hb₁ : ∃ B : ℝ, ∀ s, ‖x₁ s‖ ≤ B) (hb₂ : ∃ B : ℝ, ∀ s, ‖x₂ s‖ ≤ B) :
    Measurable (fun s => pr.f₂₀ s (x₁ s) (x₂ s)) ∧
      Integrable (fun s => pr.f₂₀ s (x₁ s) (x₂ s)) σ ∧
      ∀ i, Measurable (fun s => pr.f₂ i s (x₁ s) (x₂ s)) ∧
        ∃ B : ℝ, ∀ᵐ s ∂σ, |pr.f₂ i s (x₁ s) (x₂ s)| ≤ B := by sorry

end StochConvexProg.Duality
