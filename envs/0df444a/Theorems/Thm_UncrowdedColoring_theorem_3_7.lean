-- Prove2me | Theorems.Thm_UncrowdedColoring_theorem_3_7
-- name    : UncrowdedColoring.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:12:04.4892+00:00
-- url     : https://prove2.me/theorems/a7dbaccc-0ac3-4370-81a1-ea2c19ddd8c0
-- title:
--   Theorem 3.7 — Talagrand's inequality for Lipschitz certifiable functions of trials
-- statement:
--   Let $X$ be a non-negative integer valued random variable, not identically $0$, that is a function of independent trials $T_1,\dots,T_n$, and suppose $X$ is $\mu$-Lipschitz and $r$-certifiable for some $\mu,r>0$. Then for every $t\ge 0$,
--   $$\mathbb P\Big(|X-\mathbb E[X]|\ge t+20\mu\sqrt{r\,\mathbb E[X]}+64\mu^2r\Big)\le 4\exp\Big(-\frac{t^2}{8\mu^2r(\mathbb E[X]+t)}\Big).$$
--
--   This is the concentration tool for the list sizes and color degrees of the nibble.
--
--   **Formalization Note** The trials are the coordinates of a finite product of probability spaces with possibly different laws, and $X$ is measurable. $X$ is bounded since it is Lipschitz on a finite product, so the integral is the true expectation.
--
--   Differences from the source:
--   - encoding: X a function of n independent trials → X measurable on the finite product Measure.pi P of probability spaces; reason: the standard model of independent trials
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Theorem 3.7, p.15

import Mathlib
import Definitions.Def_UncrowdedColoring_IsLipschitzTrials

open MeasureTheory

namespace UncrowdedColoring

/-- **Theorem 3.7 (Talagrand's Inequality)**, p.15.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Theorem 3.7, p.15, with Definition 3.6.

**Formalization Note.** The trials are the coordinates of a finite product of probability spaces, with
possibly different laws, and `X` is a measurable function of them. `X` is bounded, since it is
Lipschitz on a finite product, so the Bochner integral is the true expectation. If `E[X] + t = 0` then
Lean's `0/0 = 0` makes the right side `4`, a trivially true bound. -/
theorem theorem_3_7 {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (X : (∀ i, Ω i) → ℕ) (hX : Measurable X) (hX₀ : ∃ x, X x ≠ 0)
    (μ r : ℝ) (hμ : 0 < μ) (hr : 0 < r)
    (hLip : IsLipschitzTrials X μ) (hCert : IsCertifiableTrials X r)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi P).real
        {x | t + 20 * μ * √(r * ∫ y, (X y : ℝ) ∂Measure.pi P) + 64 * μ ^ 2 * r ≤
          |(X x : ℝ) - ∫ y, (X y : ℝ) ∂Measure.pi P|} ≤
      4 * Real.exp (-(t ^ 2 / (8 * μ ^ 2 * r * ((∫ y, (X y : ℝ) ∂Measure.pi P) + t)))) := by sorry

end UncrowdedColoring
