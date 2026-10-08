-- Prove2me | Theorems.Thm_TalagrandConc_QPoints_lemma_3_1_2
-- name    : TalagrandConc.QPoints.lemma_3_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:38:36.760234+00:00
-- url     : https://prove2.me/theorems/d7a3566b-5e9b-4c14-9c8e-c8a7b43a6818
-- title:
--   Lemma 3.1.2 — $\int g^{-1}\,d\mu\,(\int g\,d\mu)^q\le 1$ for $1/q\le g\le 1$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $q\ge 2$ an integer. Let $g:\Omega\to\mathbb R$ be a measurable function with $1/q\le g\le 1$. Then
--   $$\int_\Omega \frac1g\,d\mu\,\Big(\int_\Omega g\,d\mu\Big)^q\le 1 .$$
--
--   This is the one-dimensional inequality to which the induction method reduces Theorem 3.1.1.
--
--   **Formalization Note** Measurability of $g$ is the paper's standing convention (Section 2.1); with the bounds $1/q\le g\le1$ both integrands are bounded, so the Bochner integrals are genuine.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 113, Lemma 3.1.2, Eq. (3.1.4)

import Mathlib

namespace TalagrandConc.QPoints

open MeasureTheory

/-- Lemma 3.1.2 (3.1.4). -/
theorem lemma_3_1_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) (g : Ω → ℝ) (hg : Measurable g)
    (hlow : ∀ ω, 1 / (q : ℝ) ≤ g ω) (hup : ∀ ω, g ω ≤ 1) :
    (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q ≤ 1 := by sorry

end TalagrandConc.QPoints
