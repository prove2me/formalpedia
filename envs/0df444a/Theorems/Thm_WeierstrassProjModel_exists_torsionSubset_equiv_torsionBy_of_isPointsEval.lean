-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_of_isPointsEval
-- name    : WeierstrassProjModel.exists_torsionSubset_equiv_torsionBy_of_isPointsEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/63187607-0fd1-54da-8f73-1118e17b5ea4
-- title:
--   Relative d-torsion matches E(F)[d] under a points-evaluation
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$, with structure morphism $f =$ `projModelStrCR V` from the relative Proj of the graded quotient ring of $V$ to $\operatorname{Spec} R$ (the canonical map to $\operatorname{Spec}$ of the degree-zero part, followed by $\operatorname{Spec}$ of the structural algebra map). Let $G$ be a relative group law on $f$, that is, functorial multiplication, unit and inverse operations on the sets $\{\varphi : T \to \mathrm{Proj} \mid \varphi \text{ followed by } f = t\}$ of $T$-points over $\operatorname{Spec} R$, satisfying associativity, the unit laws, left inversion and naturality in $T$. Let $ev$ assign to every field $F$ that is an $R$-algebra a bijection from the relative points over $\operatorname{Spec}$ of the structure map $R \to F$ to the group $(V \times_R F)^{\mathrm{aff}}(F)$ of affine points of the base change, and assume `IsPointsEval V G ev`: each $ev\,F$ carries the $G$-product to the sum of affine points, and carries the twist of a relative point by an $R$-algebra automorphism $\sigma$ of $F$ (precomposition with $\operatorname{Spec}\sigma$) to the image under `WeierstrassCurve.Affine.Point.map` $\sigma$. Then for every such field $F$ and every $d \in \mathbb{N}$ there exists a bijection $e$ from $\{x \mid G.\mathrm{nsmul}\,d\,x = G.\mathrm{one}\}$, the $d$-torsion relative $F$-points, onto the $\mathbb{Z}$-submodule of elements killed by $d$ in the affine point group, such that: the affine point $e\,x$ equals $ev\,F$ applied to the underlying relative point of $x$; whenever the $G$-product of two $d$-torsion points is again $d$-torsion, $e$ of that product equals $e\,x + e\,y$; and whenever the $\sigma$-twist of a $d$-torsion point $x$ is again $d$-torsion, $e$ of the twist equals the image of $e\,x$ under `Point.map` $\sigma$.
--
--   This transports the $d$-torsion of an abstractly given relative group law on the projective model of a Weierstrass curve onto the classical $d$-torsion subgroup $E(F)[d]$ of the affine point group, respecting addition and the Galois action. It is used in the construction of the Hopf-algebra/Galois-module description of torsion attached to such a group law, via [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_of_isPointsEval.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.Algebra.Module.Torsion.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.exists_torsionSubset_equiv_torsionBy_of_isPointsEval
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev)
    (F : Type u) [Field F] [DecidableEq F] [Algebra R F] (d : ℕ) :
    ∃ e : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d) ≃
        ↥(Submodule.torsionBy ℤ (V.baseChange F).toAffine.Point (d : ℤ)),
      (∀ x : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          (e x : (V.baseChange F).toAffine.Point) = ev F x.1) ∧
      (∀ (x y : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d))
          (hxy : G.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) x.1 y.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          e ⟨_, hxy⟩ = e x + e y) ∧
      (∀ (σ : F ≃ₐ[R] F)
          (x : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d))
          (hσx : galTwist σ x.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          (e ⟨_, hσx⟩ : (V.baseChange F).toAffine.Point) =
            WeierstrassCurve.Affine.Point.map (σ : F →ₐ[R] F)
              (e x : (V.baseChange F).toAffine.Point)) := by sorry
