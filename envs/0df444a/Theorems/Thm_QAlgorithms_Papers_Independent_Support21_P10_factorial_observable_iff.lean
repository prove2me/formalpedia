-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P10_factorial_observable_iff
-- name    : QAlgorithms.Papers.Independent.Support21.P10.factorial_observable_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:54:58.70721+00:00
-- url     : https://prove2.me/theorems/703537f5-7eb7-4bf5-9f6e-21ca3cfd227f
-- title:
--   Factorial varieties: dense closed orbits and semiinvariant characters
-- statement:
--   Let $k$ be an algebraically closed field of arbitrary characteristic, let $G$ be a smooth affine algebraic group of finite type over $k$, and let $X$ be a reduced affine $k$-variety of finite type with a regular $G$-action. Assume $k[X]$ is a unique factorization domain. Let $\Omega(X)$ be the locus of closed orbits of maximal dimension. Let $E_G(X)$ be the regular characters $\chi:G\to\mathbb G_m$ admitting a nonzero $\chi$-semiinvariant in $k[X]$. Then
--
--   $$
--   G\curvearrowright X\text{ is observable}\quad\Longleftrightarrow\quad \bigl[\exists U\subseteq\Omega(X),\ U\text{ open and dense in }X\bigr]\ \text{ and }\ E_G(X)\text{ is a group}.
--   $$
--
--   The group condition is closure under inverse characters: nonzero semiinvariants multiply to nonzero semiinvariants in the domain, and the trivial character is represented by $1$. Both conditions are required for this factorial criterion.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, PDF p. 11, Corollary 3.15

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- PDF p.11, Corollary 3.15: for a factorial affine variety,
observability is equivalent to BOTH a dense open subset of Omega(X) and
the group property of E_G(X). Factoriality includes the domain hypothesis;
the density and the character condition are separate conjuncts. -/
theorem factorial_observable_iff
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    IsObservable rho ↔
      (∃ U : Set (Point k A), IsClassicallyOpen U ∧ IsClassicallyDense U ∧
        U ⊆ omegaLocus rho) ∧ SemiInvariantCharactersFormGroup rho := by sorry

end QAlgorithms.Papers.Independent.Support21.P10

end
