-- Prove2me | Theorems.Thm_WeakMFG_Existence_lemma_7_6
-- name    : WeakMFG.Existence.lemma_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:44.24498+00:00
-- url     : https://prove2.me/theorems/cdb15567-ea21-4774-abb9-5404bad3ad32
-- title:
--   Lemma 7.6 — the density of an image measure is the conditional expectation of the density
-- statement:
--   Let $(E,\mathcal E)$ and $(F,\mathcal F)$ be measurable spaces, let $\mu,\nu$ be probability measures on $E$ with $\nu\ll\mu$, and let $X:E\to F$ be measurable. Then
--   $$\frac{d\,\nu\circ X^{-1}}{d\,\mu\circ X^{-1}}\circ X=\mathbb E^{\mu}\Big[\frac{d\nu}{d\mu}\,\Big|\,X\Big]\qquad\mu\text{-a.s.}$$
--
--   In the paper this transfers bounds on the density $dP^{\mu,\alpha}/dP$ to the density of the law $P^{\mu,\alpha}\circ X^{-1}$ with respect to $\mathcal X=P\circ X^{-1}$ (Lemma 7.7).
--
--   **Formalization Note** Radon–Nikodym derivatives are Mathlib's `rnDeriv`, turned into real numbers; the conditional expectation is taken given the $\sigma$-field $\sigma(X)$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 7.6, p. 24

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- Lemma 7.6 (Carmona–Lacker, arXiv:1307.1152v2, p. 24): let `(E, ℰ)`, `(F, ℱ)` be measurable
spaces, `μ, ν ∈ P(E)` with `ν ≪ μ`, and `X : E → F` measurable. Then
`d(ν ∘ X⁻¹)/d(μ ∘ X⁻¹) ∘ X = E^μ[dν/dμ | X]` `μ`-a.s.
Formalization Note: Radon–Nikodym derivatives are Mathlib's `rnDeriv` (in `ℝ≥0∞`, real-valued via
`toReal`); `E^μ[· | X]` is the conditional expectation given `σ(X) = ℱ.comap X`. -/
theorem lemma_7_6 {E F : Type*} [MeasurableSpace E] [mF : MeasurableSpace F]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ)
    (X : E → F) (hX : Measurable X) :
    (fun x => ((ν.map X).rnDeriv (μ.map X) (X x)).toReal) =ᵐ[μ]
      μ[fun x => (ν.rnDeriv μ x).toReal | MeasurableSpace.comap X mF] := by sorry

end WeakMFG.Existence
