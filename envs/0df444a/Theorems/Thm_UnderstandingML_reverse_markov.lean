-- Prove2me | Theorems.Thm_UnderstandingML_reverse_markov
-- name    : UnderstandingML.reverse_markov
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:32:03.865754+00:00
-- url     : https://prove2.me/theorems/fc40eb92-0d7d-4af3-9ebd-6c60d8814cba
-- title:
--   Lemma B.1: for Z ∈ [0,1] with E[Z] = μ and a ∈ (0,1), P[Z > 1 − a] ≥ (μ − (1 − a))/a and P[Z > a] ≥ (μ − a)/(1 − a) ≥ μ − a
-- statement:
--   **Lemma B.1.** Let $Z$ be a random variable that takes values in $[0,1]$. Assume that $E[Z] = \mu$. Then, for any $a \in (0,1)$,
--   $$P[Z > 1 - a] \ge \frac{\mu - (1-a)}{a}.$$
--   This also implies that for every $a \in (0,1)$,
--   $$P[Z > a] \ge \frac{\mu - a}{1 - a} \ge \mu - a.$$
--
--   Formally: for a probability measure $D$ on $\Omega$, a measurable $\theta : \Omega \to \mathbb{R}$ with $\theta \in [0,1]$ $D$-almost surely, $\mu = \int \theta\,dD$ and $a \in (0,1)$, the three inequalities hold with $P[\cdot] = D(\cdot)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Appendix B.1 p. 422, Lemma B.1 with its proof (from Markov's inequality (B.3))

import Definitions.Def_UnderstandingML_Framework
import Mathlib.SetTheory.Cardinal.Finite

open MeasureTheory

namespace UnderstandingML

/-- **Lemma B.1** (p. 422). Let `Z` be a random variable that takes values in `[0, 1]` and assume
that `E[Z] = μ`. Then for any `a ∈ (0, 1)`, `P[Z > 1 − a] ≥ (μ − (1 − a))/a`. This also implies
that for every `a ∈ (0, 1)`, `P[Z > a] ≥ (μ − a)/(1 − a) ≥ μ − a`. Stated for a measurable
`θ : Ω → ℝ` with values in `[0, 1]` almost surely under a probability measure `D`, with
`μ = ∫ θ dD`. -/
theorem reverse_markov {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (θ : Ω → ℝ) (hθ : Measurable θ) (hrange : ∀ᵐ ω ∂D, θ ω ∈ Set.Icc (0 : ℝ) 1) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    ((∫ ω, θ ω ∂D) - (1 - a)) / a ≤ (D {ω | 1 - a < θ ω}).toReal ∧
    ((∫ ω, θ ω ∂D) - a) / (1 - a) ≤ (D {ω | a < θ ω}).toReal ∧
    (∫ ω, θ ω ∂D) - a ≤ (D {ω | a < θ ω}).toReal := by sorry

end UnderstandingML
