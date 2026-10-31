-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P17_os_contraction_representation
-- name    : QAlgorithms.Papers.Independent.Intake100.P17.os_contraction_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:24:21.905675+00:00
-- url     : https://prove2.me/theorems/95d41fcb-1691-4132-9c07-acfb89c64012
-- title:
--   OS quotient: induced star-semigroup contractions
-- statement:
--   Let \(G\) be a group, \(\tau\) an involutive automorphism, and \(S\subseteq G\) a subsemigroup stable under \(s^\sharp=\tau(s)^{-1}\). Let \(E\) be a complex Hilbert space carrying a unitary representation \(\pi\) and a unitary involution \(\theta\) with \(\theta\pi(g)\theta=\pi(\tau(g))\). Suppose that the closed complex subspace \(E_+\) is invariant under \(S\) and that the form \(\langle\theta v,v\rangle\) is nonnegative for every \(v\in E_+\). Inner products in this statement are linear in the first variable.
--
--   There exists a realization \(\widehat E\) of the Hilbert completion of \(E_+/N\), where \(N=\{v:\langle\theta v,v\rangle=0\}\), with dense linear quotient map \(q\), and bounded operators \(\widehat\pi(s)\) satisfying
--   \[
--   \widehat\pi(s)q(v)=q(\pi(s)v),\qquad
--   \|\widehat\pi(s)\|\le1,\qquad
--   \widehat\pi(st)=\widehat\pi(s)\widehat\pi(t),\qquad
--   \widehat\pi(s)^*=\widehat\pi(s^\sharp).
--   \]
--   The quotient has \(\langle q(v),q(w)\rangle=\langle\theta v,w\rangle\), its kernel is exactly \(N\), and the displayed action is independent of the representative. Thus the formula defines a representation of the involutive semigroup by contractions.
--
--   This is the passage from reflection-positive unitary actions to the OS semigroup. **Formalization Note** The completion is existential output with a dense form-preserving map, a characterization of the source's quotient completion up to its canonical unitary isomorphism; it is not an input hypothesis. Mathlib inner products have the opposite linearity convention.
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, PDF p. 7, Lemma 1.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Lemma 1.4, PDF p. 7: quotient descent and extension produce a star-semigroup
representation by contractions. The completion and every induced operator are conclusions. -/
theorem os_contraction_representation
    {G E : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (tau : G ≃* G) (htau : Function.Involutive tau)
    (S : Subsemigroup G) (hsharp : ∀ s ∈ S, (tau s)⁻¹ ∈ S)
    (R : ReflectionAction G tau E) (P : Submodule ℂ E) (hclosed : IsClosed (P : Set E))
    (hpos : ThetaPositive R.theta P)
    (hstable : ∀ s ∈ S, ∀ v ∈ P, R.pi s v ∈ P) :
    ∃ C : OSCompletion P R.theta,
      ∃ rho : S → C.Carrier →L[ℂ] C.Carrier,
        (∀ s, ∀ v : P,
          rho s (C.quotientMap v) = C.quotientMap ⟨R.pi s v, hstable s s.property v v.property⟩) ∧
        (∀ s, ‖rho s‖ ≤ 1) ∧
        (∀ s t : S, rho (s * t) = (rho s).comp (rho t)) ∧
        (∀ s : S, (rho s).adjoint = rho ⟨(tau s)⁻¹, hsharp s s.property⟩) ∧
        (∀ v : P, C.quotientMap v = 0 ↔ inner ℂ (v : E) (R.theta v) = 0) ∧
        (∀ (s : S) (v w : P), C.quotientMap v = C.quotientMap w →
          C.quotientMap ⟨R.pi s v, hstable s s.property v v.property⟩ =
          C.quotientMap ⟨R.pi s w, hstable s s.property w w.property⟩) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P17

end
