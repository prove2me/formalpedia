-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_bounded_composition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_bounded_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:18:17.163628+00:00
-- url     : https://prove2.me/theorems/ed6f6677-beba-498a-b3dc-effa5b93c472
-- title:
--   Unnumbered main result (composition rule (7.1))
-- statement:
--   Let $A$ be a bounded normal operator on a complex Hilbert space, and let $f,g:\mathbb C\to\mathbb C$ be finite-valued Borel functions. Assume $f(A)$ is bounded, with evaluations taken in the unique associated Borel calculi. Then
--
--   $$g(f(A))=(g\circ f)(A).$$
--
--   There is no boundedness assumption on $g$, and equality includes domains.
--
--   This is the bounded-operator composition rule (7.1).
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 32, Unnumbered main result (composition rule (7.1))

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Composition rule (7.1), PDF p.32: bounded A and f(A), with arbitrary Borel g.
Source correction (independently audited in moderation round 1).
Printed: The context of equation (7.1) writes f in Bo(C), although Bo(C) denotes a sigma algebra of sets.
Changed: Take f to be a finite-valued Borel measurable function C to C, with bounded f(A).
Why: Phi_A(f) and g composed with f require a function. The notation M(C), the definition of the calculus and the proof determine this type. Bounded normal A, bounded f(A) and arbitrary Borel g are retained.
-/
theorem spectral_bounded_composition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Relation E) (hA : Normal (k := ℂ) A) (hbA : BoundedOperator (k := ℂ) A)
    (f g : Symbol ℂ ℂ) (hbf : BoundedOperator (k := ℂ) (spectralValue A f)) :
    spectralValue (spectralValue A f) g = spectralValue A (compose g f.val f.property) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
