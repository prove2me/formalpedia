-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P01_classicalNESSPositivity
-- name    : QAlgorithms.Papers.Independent.Next46.P01.classicalNESSPositivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:32:00.760388+00:00
-- url     : https://prove2.me/theorems/9a842dec-2d0b-4a8e-a32a-747a6c746206
-- title:
--   Every classical Cesaro NESS is invariant and has nonnegative entropy production
-- statement:
--   Let $(X,\phi,\omega)$ satisfy the compact classical assumptions (Cl1)–(Cl3), with non-invariant reference probability $\omega$ and continuous entropy production observable $\sigma$. A nonequilibrium steady state is any weak cluster point, as $T\to+\infty$, of the Cesaro probabilities
--   $$
--   \frac1T\int_0^T\omega_t\,dt.
--   $$
--   The set of these states is nonempty. Every such Borel probability $\omega_+$ satisfies
--   $$
--   (\phi_t)_*\omega_+=\omega_+\quad(t\in\mathbb R),\qquad
--   \int_X\sigma\,d\omega_+\ge0.
--   $$
--   This statement concerns every cluster NESS; neither convergence to a unique state nor absolute continuity of that state is assumed. The weak-cluster condition is expressed by finite families of continuous test functions and arbitrarily large positive averaging times.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, PDF p. 23, classical-ness-positivity

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

noncomputable section

open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

section Classical

variable (X : Type*) [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

variable {X}

/-- Classical Cesaro NESS existence, invariance and entropy production positivity:
arXiv:2409.15485v2, PDF p.23. This quantifies over every cluster NESS and
requires no (Cl4), uniqueness, or normality of that state. -/
theorem classicalNESSPositivity (D : RegularClassicalSystem X)
    (hnoninvariant : ClassicalNonInvariant D.toClassicalFlowSystem) :
    (∃ nu : ProbabilityMeasure X, IsClassicalNESS D.toClassicalFlowSystem nu) ∧
      ∀ nu : ProbabilityMeasure X, IsClassicalNESS D.toClassicalFlowSystem nu →
        (∀ t : ℝ, classicalEvolved D.toClassicalFlowSystem (nu : Measure X) t =
          (nu : Measure X)) ∧
        0 ≤ ∫ x, classicalProduction D x ∂(nu : Measure X) := by sorry

end Classical

end QAlgorithms.Papers.Independent.Next46.P01

end
