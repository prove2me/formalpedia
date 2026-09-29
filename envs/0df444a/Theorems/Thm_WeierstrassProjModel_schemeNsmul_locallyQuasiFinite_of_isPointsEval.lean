-- Prove2me | Theorems.Thm_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval
-- name    : WeierstrassProjModel.schemeNsmul_locallyQuasiFinite_of_isPointsEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/01f13dcb-e5a2-558f-b54d-5624493da386
-- title:
--   Multiplication by n on the projective Weierstrass model is locally quasi-finite
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$, with projective model $\mathrm{Proj}$ of the quotient grading attached to $V$ and structure morphism `projModelStrCR V` to $\operatorname{Spec} R$ (the canonical map to $\operatorname{Spec}$ of the degree-zero part, followed by $\operatorname{Spec}$ of the structure map of $R$). Four hypotheses are assumed: (hbc) for every field $K$ which is an $R$-algebra, the fibre product of `projModelStrCR V` with $\operatorname{Spec} K \to \operatorname{Spec} R$ is isomorphic to the projective model of the base change $V_K$; $G$ is a relative group law on `projModelStrCR V`, i.e. for every scheme $T$ with a morphism $t$ to $\operatorname{Spec} R$ a multiplication, unit and inverse on the set of $T$-points over $t$ (morphisms $T \to$ model commuting with $t$) satisfying associativity, the unit laws, left inverse and naturality in $T$; (ev) for every field $F$ which is an $R$-algebra, a bijection between the set of such points over $\operatorname{Spec} F \to \operatorname{Spec} R$ and the group of points of the affine curve $V_F$; (hev) these bijections satisfy `IsPointsEval V G ev`, namely each carries the multiplication of $G$ to addition of points, and intertwines precomposition with $\operatorname{Spec}$ of an $R$-algebra automorphism $\sigma$ of $F$ with the induced map on points; (hℓ) for every algebraically closed field $F$ which is an $R$-algebra and every prime $\ell$ with $\ell \neq 0$ in $F$, the curve $V_F$ has a nonzero point killed by $\ell$. The conclusion is that for every $n > 0$ the endomorphism `G.schemeNsmul n` of the model — the underlying morphism of the $n$-fold $G$-sum of the identity point, i.e. multiplication by $n$ — is locally quasi-finite.
--
--   This records that multiplication by a positive integer on the projective Weierstrass model, viewed as a morphism of schemes over $\operatorname{Spec} R$, has discrete fibres. It is used in the construction of Néron models towards the finiteness and flatness of the $n$-torsion: it feeds the proofs that the fibrewise endomorphism induced by multiplication by $n$ is flat for elliptic $V$, and that the kernel of multiplication by $n$ is finite over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_schemeNsmul_locallyQuasiFinite_of_isPointsEval.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.schemeNsmul_locallyQuasiFinite_of_isPointsEval
    {R : Type u} [CommRing R]
    (V : WeierstrassCurve.Projective R)
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev)
    (hℓ : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 →
      ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0) :
    ∀ n : ℕ, 0 < n → LocallyQuasiFinite (G.schemeNsmul n) := by sorry
