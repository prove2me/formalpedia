-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P10_affinizedQuotient_universal
-- name    : QAlgorithms.Papers.Independent.Support21.P10.affinizedQuotient_universal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:52:26.54763+00:00
-- url     : https://prove2.me/theorems/d46cb0e4-0f91-456a-b1b7-8bfe5647af3e
-- title:
--   Universal property of the affinized quotient for affine targets
-- statement:
--   Let $k$ be an algebraically closed field of arbitrary characteristic, let $G$ be a smooth affine algebraic group of finite type over $k$, and let $X$ be a reduced affine $k$-variety of finite type with a regular $G$-action. Suppose $B=k[X]^G$ is finitely generated, and let $\pi:X\to Y=\operatorname{Spec}B$ be induced by $B\hookrightarrow k[X]$. Let $Z$ be a reduced affine $k$-variety of finite type, and let $f:X\to Z$ be a regular morphism constant on $G$-orbits. Then
--
--   $$
--   \exists!\,\widetilde f:Y\to Z\text{ regular},\qquad \widetilde f\circ\pi=f.
--   $$
--
--   This is the universal property in the category of affine varieties. In coordinate rings it is the unique factorization of $f^*:k[Z]\to k[X]$ through the actual inclusion $B\hookrightarrow k[X]$.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, PDF p. 4, §2, unnumbered: universal property of the affinized quotient

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- PDF p.4, unnumbered universal property following Definition 2.8:
every geometricOrbit-constant regular map to an affine variety factors uniquely through
the canonical affinized quotient. Equality is the commuting pullback diagram,
not just equality on points or an abstract algebra isomorphism. -/
theorem affinizedQuotient_universal
    {k : Type u} {H : Type v} {A : Type w} {B : Type z}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [CommRing B]
    [Algebra k H] [Algebra k A] [Algebra k B] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (hZ : IsAffineVariety k B) (rho : Point k H →* (A ≃ₐ[k] A))
    (hregular : IsRegularAction rho)
    (hfg : Algebra.FiniteType k (invariantSubalgebra rho))
    (f : B →ₐ[k] A) (hf : IsConstantOnOrbits rho f) :
    ∃! lift : B →ₐ[k] invariantSubalgebra rho,
      (invariantSubalgebra rho).val.comp lift = f := by sorry

end QAlgorithms.Papers.Independent.Support21.P10

end
