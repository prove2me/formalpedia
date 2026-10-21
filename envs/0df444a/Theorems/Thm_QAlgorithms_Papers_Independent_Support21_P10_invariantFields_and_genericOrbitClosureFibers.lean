-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P10_invariantFields_and_genericOrbitClosureFibers
-- name    : QAlgorithms.Papers.Independent.Support21.P10.invariantFields_and_genericOrbitClosureFibers
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:53:51.673387+00:00
-- url     : https://prove2.me/theorems/b7bba9b2-6876-4adc-bf28-f8dbfe8e0c82
-- title:
--   Generic orbit-closure fibers and invariant-field extensions
-- statement:
--   Let $k$ be an algebraically closed field of arbitrary characteristic, let $G$ be a smooth affine algebraic group of finite type over $k$, and let $X$ be a reduced affine $k$-variety of finite type with a regular $G$-action. Assume $X$ is irreducible and $B=k[X]^G$ is finitely generated. Let $\pi:X\to Y=\operatorname{Spec}B$ be the canonical affinized quotient and let $X_{\max}$ be the locus of maximal-dimensional orbits. If $\operatorname{Frac}(B)=k(X)^G$ canonically inside $k(X)$, then there is $0\ne f\in B$ such that $Y_f$ is nonempty and
--
--   $$
--   \forall z\in Y_f,\quad \exists y\in X_{\max},\quad \pi^{-1}(z)=\overline{G\cdot y}.
--   $$
--
--   Moreover $Y_f$ is canonically the affinized quotient of $X_f$. Conversely, if this fiber formula holds over any nonempty open subset of $Y$, then
--
--   $$
--   \operatorname{Frac}(B)\subseteq k(X)^G\text{ is finite and purely inseparable};\qquad \operatorname{char}k=0\Longrightarrow\operatorname{Frac}(B)=k(X)^G.
--   $$
--
--   Finiteness means finite dimension over the canonical smaller field. Pure inseparability means that each invariant rational function has a $p$-power in that field, with characteristic exponent $p=1$ in characteristic zero. The theorem links generic quotient fibers to the invariant function field; the fibers are orbit closures, and the orbits need not themselves be closed.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, PDF p. 7, Theorem 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- PDF pp.7--9, Theorem 3.7. Equality of the invariant fraction fields
implies a nonempty principal-open locus in the affinized quotient with
geometricOrbit-closure fibers through X_max, including the canonical principal-open
quotient identification. Conversely the nonempty-open fiber condition
implies a finite purely inseparable extension of the two canonical invariant
fields, and equality in characteristic zero. G need not be connected.
The closure bar is essential; closedness of the orbits is not asserted. -/
theorem invariantFields_and_genericOrbitClosureFibers
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho)
    (hfg : Algebra.FiniteType k (invariantSubalgebra rho)) :
    (InvariantFractionFieldsEqual rho →
      ∃ f : invariantSubalgebra rho, (f : A) ≠ 0 ∧
        (principalOpen (k := k) f).Nonempty ∧
        HasOrbitClosureFibersOver rho (principalOpen f) ∧
        ∃ e : Localization.Away f ≃ₐ[k] localizedInvariantSubalgebra rho f,
          (localizedInvariantSubalgebra rho f).val.comp e.toAlgHom =
            invariantLocalizationMap rho f) ∧
    (HasGenericOrbitClosureFibers rho →
      FinitePurelyInseparableInvariantExtension rho ∧
        (ringChar k = 0 → InvariantFractionFieldsEqual rho)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P10

end
