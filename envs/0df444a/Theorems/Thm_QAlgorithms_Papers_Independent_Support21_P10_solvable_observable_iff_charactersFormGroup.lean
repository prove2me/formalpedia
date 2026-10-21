-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P10_solvable_observable_iff_charactersFormGroup
-- name    : QAlgorithms.Papers.Independent.Support21.P10.solvable_observable_iff_charactersFormGroup
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:55:31.157994+00:00
-- url     : https://prove2.me/theorems/6a9fd19d-167e-4cff-aaa1-574da0f180dc
-- title:
--   Solvable groups: observability and semiinvariant characters
-- statement:
--   Let $k$ be an algebraically closed field of arbitrary characteristic, let $G$ be a smooth affine algebraic group of finite type over $k$, and let $X$ be a reduced affine $k$-variety of finite type with a regular $G$-action. Assume $X$ is irreducible and $G$ is solvable. Let $E_G(X)$ consist of the regular characters $\chi:G\to\mathbb G_m$ for which some $0\ne a\in k[X]$ satisfies $g\cdot a=\chi(g)a$ for every $g\in G(k)$. Then
--
--   $$
--   G\curvearrowright X\text{ is observable}\quad\Longleftrightarrow\quad E_G(X)\text{ is a group}.
--   $$
--
--   Equivalently every represented character has its inverse represented by a nonzero semiinvariant. This criterion requires no separate condition on the closed-orbit locus and no finite generation of the invariant algebra.
--
--   **Formalization Note** Irreducibility records the contextual domain reading on pp.1–2 used by the monoid argument. Solvability is the derived-series condition on $G(k)$, equivalent to algebraic solvability over the algebraically closed base field.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, PDF p. 11, Corollary 3.16

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- PDF p.11, Corollary 3.16: for a solvable affine algebraic group acting
on an irreducible affine variety, observability is equivalent to E_G(X)
being a group. The domain hypothesis records the contextual irreducible
reading pinned in the plan; it prevents products of nonzero semiinvariants
from becoming zero on different components. Solvability is that of G(k),
equivalently the algebraic derived-series condition over algebraically closed k.
No geometricOrbit-locus hypothesis or finite-generation assumption on k[X]^G is added. -/
theorem solvable_observable_iff_charactersFormGroup
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    [Group.IsSolvable (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    IsObservable rho ↔ SemiInvariantCharactersFormGroup rho := by sorry

end QAlgorithms.Papers.Independent.Support21.P10

end
