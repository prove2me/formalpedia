-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P10_invariantLocalization_separatesMaximalOrbits
-- name    : QAlgorithms.Papers.Independent.Support21.P10.invariantLocalization_separatesMaximalOrbits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:54:23.234741+00:00
-- url     : https://prove2.me/theorems/729d5096-93f0-4b08-8e72-f7503e24ec0a
-- title:
--   Generic separation by localized invariants
-- statement:
--   Let $k$ be an algebraically closed field of arbitrary characteristic, let $G$ be a smooth affine algebraic group of finite type over $k$, and let $X$ be a reduced affine $k$-variety of finite type with a regular $G$-action. Assume $X$ is irreducible and $\operatorname{Frac}(k[X]^G)=k(X)^G$ via the canonical inclusion. Let $X_{\max}$ be the locus of maximal-dimensional orbits. There exists $0\ne f\in k[X]^G$ with $X_f\ne\varnothing$ such that
--
--   $$
--   \forall x,y\in X_{\max}\cap X_f,\quad G\cdot x\ne G\cdot y\Longrightarrow\exists h\in (k[X]^G)_f,\ h(x)\ne h(y).
--   $$
--
--   Here localization consists of fractions $a/f^n$ with $a\in k[X]^G$ and $n\ge0$. All evaluations occur on $X_f$, so their denominators are nonzero. This gives separation on a nonempty generic locus without assuming that the whole invariant algebra is finitely generated.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, PDF p. 9, Corollary 3.9

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- PDF p.9, Corollary 3.9: a nonempty invariant principal open admits
separation of its maximal-dimensional orbits by the localized invariant
algebra. The source's proof supplies f nonzero and X_f nonempty; these are
recorded to exclude the vacuous empty-open reading. Elements of (k[X]^G)_f
are written as a/f^n, and both evaluations have nonzero denominators.
No finite generation of k[X]^G is assumed. -/
theorem invariantLocalization_separatesMaximalOrbits
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho)
    (hfields : InvariantFractionFieldsEqual rho) :
    ∃ f : invariantSubalgebra rho, (f : A) ≠ 0 ∧
      (principalOpen (k := k) (f : A)).Nonempty ∧
      ∀ x y : Point k A,
        x ∈ maximalOrbitLocus rho → x ∈ principalOpen (f : A) →
        y ∈ maximalOrbitLocus rho → y ∈ principalOpen (f : A) →
        y ∉ geometricOrbit rho x →
        ∃ a : invariantSubalgebra rho, ∃ n : ℕ,
          x (a : A) / x (f : A) ^ n ≠ y (a : A) / y (f : A) ^ n := by sorry

end QAlgorithms.Papers.Independent.Support21.P10

end
