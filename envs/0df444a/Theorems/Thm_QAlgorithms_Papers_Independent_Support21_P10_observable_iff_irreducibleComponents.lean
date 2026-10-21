-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P10_observable_iff_irreducibleComponents
-- name    : QAlgorithms.Papers.Independent.Support21.P10.observable_iff_irreducibleComponents
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:53:21.53481+00:00
-- url     : https://prove2.me/theorems/1c0b1cd7-6c3d-4db5-987a-a5c84992a86e
-- title:
--   Observability on the computed irreducible components
-- statement:
--   Let $k$ be an algebraically closed field of arbitrary characteristic, let $G$ be a smooth affine algebraic group of finite type over $k$, and let $X$ be a reduced affine $k$-variety of finite type with a regular $G$-action. Assume $G$ is connected. Let $X_1,\ldots,X_n$ be the irreducible components of $X$, computed from $X$ itself. Then
--
--   $$
--   G\curvearrowright X\text{ is observable}\quad\Longleftrightarrow\quad \forall i,\ G\curvearrowright X_i\text{ is observable}.
--   $$
--
--   Connectedness ensures that each component is stable. In coordinate rings the components are $\operatorname{Spec}(A/P)$ for the minimal primes $P$ of $A=k[X]$, and each induced action is fixed by its compatibility with $A\twoheadrightarrow A/P$. This reduces observability to the actual components while retaining reducible varieties.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, PDF p. 5, Lemma 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- PDF p.5, Lemma 3.1. The irreducible components are the spectra
of A/P for the COMPUTED minimal primes P of A. Connectedness of G is
connectedness of Spec k[G]. The component action is pinned by the
surjective quotient pullback, so it cannot be an unrelated action. Existence
of that induced action also records the component stability guaranteed by
connectedness. X is allowed to be reducible or empty. -/
theorem observable_iff_irreducibleComponents
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    [ConnectedSpace (PrimeSpectrum H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    IsObservable rho ↔
      ∀ P : Ideal A, P ∈ minimalPrimes A →
        ∃ rhoP : Point k H →* ((A ⧸ P) ≃ₐ[k] (A ⧸ P)),
          (∀ g : Point k H, ∀ a : A,
            rhoP g (Ideal.Quotient.mkₐ k P a) = Ideal.Quotient.mkₐ k P (rho g a)) ∧
          IsObservable rhoP := by sorry

end QAlgorithms.Papers.Independent.Support21.P10

end
