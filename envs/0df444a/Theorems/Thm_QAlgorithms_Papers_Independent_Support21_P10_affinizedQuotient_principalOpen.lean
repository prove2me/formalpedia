-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P10_affinizedQuotient_principalOpen
-- name    : QAlgorithms.Papers.Independent.Support21.P10.affinizedQuotient_principalOpen
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:52:47.620985+00:00
-- url     : https://prove2.me/theorems/9751e43a-e00c-4e9b-ac64-4278b17129ed
-- title:
--   Localization of the canonical affinized quotient
-- statement:
--   Let $k$ be an algebraically closed field of arbitrary characteristic, let $G$ be a smooth affine algebraic group of finite type over $k$, and let $X$ be a reduced affine $k$-variety of finite type with a regular $G$-action. Assume $B=k[X]^G$ is finitely generated, and let $\pi:X\to Y=\operatorname{Spec}B$ be the canonical affinized quotient. For every $f\in B$, define $X_f=\{x:f(x)\ne0\}$ and $Y_f=\{y:f(y)\ne0\}$. Then
--
--   $$
--   \pi|_{X_f}:X_f\longrightarrow Y_f\text{ is the affinized quotient},\qquad B_f\xrightarrow{\sim} (k[X]_f)^G.
--   $$
--
--   The displayed algebra isomorphism is the canonical localization of $B\hookrightarrow k[X]$ followed by restriction to its invariant image. Thus its inclusion into $k[X]_f$ is the actual restriction map. The statement includes $f=0$, when both principal opens are empty and both localized coordinate rings are zero. It allows the affinized quotient to be restricted canonically to principal open subsets.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, PDF p. 5, Lemma 2.10

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- PDF p.5, Lemma 2.10. The canonical localization of the invariant inclusion
identifies (k[X]^G)_f with (k[X]_f)^G; contravariantly this identifies the
restriction of pi to X_f with its affinized quotient onto (X/aff G)_f.
The equality of maps preserves the canonical restriction identification.
There is deliberately no nonzero or non-zero-divisor hypothesis on f. -/
theorem affinizedQuotient_principalOpen
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho)
    (hfg : Algebra.FiniteType k (invariantSubalgebra rho))
    (f : invariantSubalgebra rho) :
    ∃ e : Localization.Away f ≃ₐ[k] localizedInvariantSubalgebra rho f,
      (localizedInvariantSubalgebra rho f).val.comp e.toAlgHom =
        invariantLocalizationMap rho f := by sorry

end QAlgorithms.Papers.Independent.Support21.P10

end
