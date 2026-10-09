-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_lemma_5
-- name    : ResidualsDRO.Wass.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:10:10.443852+00:00
-- url     : https://prove2.me/theorems/47f57021-cead-43ff-b3de-c9864ef99002
-- title:
--   Lemma 5, p. 14 — P(V + W > C₁ + C₂) ≤ P(V > C₁) + P(W > C₂)
-- statement:
--   Let $V$ and $W$ be real random variables on a probability space $(\Omega,\mathbb P)$ and $C_1,C_2\in\mathbb R$. Then
--   $$\mathbb P(V+W>C_1+C_2)\le\mathbb P(V>C_1)+\mathbb P(W>C_2).$$
--
--   This union-bound inequality combines the two error allowances of the radius in Lemma 6 and in the proof of Theorem 7.
--
--   **Formalization Note** Probabilities are outer measures of the displayed sets, so $V$ and $W$ need not be measurable.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 14, Lemma 5

import Mathlib

open MeasureTheory

namespace ResidualsDRO.Wass

/-- Lemma 5, p. 14. For real random variables `V, W` on `(Ω, P)` and constants `C₁, C₂ ∈ ℝ`,
`P(V + W > C₁ + C₂) ≤ P(V > C₁) + P(W > C₂)`. Probabilities are (outer) measures of the
displayed sets, so no measurability is required. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V W : Ω → ℝ) (C₁ C₂ : ℝ) :
    P {ω | C₁ + C₂ < V ω + W ω} ≤ P {ω | C₁ < V ω} + P {ω | C₂ < W ω} := by sorry

end ResidualsDRO.Wass
