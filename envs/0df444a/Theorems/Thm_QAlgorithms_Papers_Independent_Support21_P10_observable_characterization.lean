-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P10_observable_characterization
-- name    : QAlgorithms.Papers.Independent.Support21.P10.observable_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:52:03.820578+00:00
-- url     : https://prove2.me/theorems/0a257446-ccef-411a-99b2-7f0e024d6f75
-- title:
--   Observability, invariant rational functions, and generic closed orbits
-- statement:
--   Let $k$ be an algebraically closed field of arbitrary characteristic, let $G$ be a smooth affine algebraic group of finite type over $k$, and let $X$ be a reduced affine $k$-variety of finite type with a regular $G$-action. Assume that $X$ is irreducible. Write $A=k[X]$, $B=A^G$, and let $\Omega(X)$ consist of the points whose orbits are closed and have maximal dimension among all orbits in $X$. An action is observable if every nonzero $G$-stable ideal of $A$ contains a nonzero invariant. Then
--
--   $$
--   G\curvearrowright X\text{ is observable}\quad\Longleftrightarrow\quad k(X)^G=\operatorname{Frac}(B)\ \text{ and }\ \Omega(X)\text{ contains a nonempty open subset}.
--   $$
--
--   The equality uses the canonical inclusions into $k(X)$. On irreducible $X$, the open-locus condition is equivalent to the abstract's condition that a nonempty open subset consists of closed orbits: intersect that subset with $X_{\max}$. This characterizes precisely when stable ideals have nonzero invariant elements.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, PDF p. 1, Abstract main characterization; Theorem 3.10

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- PDF p.1, abstract, and PDF pp.9--10, Theorem 3.10: observability
is equivalent to the canonical equality of invariant fraction fields and
a nonempty open locus in Omega(X). On irreducible X this is equivalent to
the abstract's nonempty open locus of closed orbits, by intersection with
X_max. No finite-generation assumption on the invariant algebra is imposed. -/
theorem observable_characterization
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho) :
    IsObservable rho ↔
      InvariantFractionFieldsEqual rho ∧ ContainsNonemptyOpen (omegaLocus rho) := by sorry

end QAlgorithms.Papers.Independent.Support21.P10

end
