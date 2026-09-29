-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_galoisEquivariant
-- name    : WeierstrassProjModel.exists_torsionSubset_equiv_torsionBy_galoisEquivariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/ec2e9c72-3010-591e-98b9-b67e418d1fd8
-- title:
--   Galois-equivariant bijection between relative d-torsion and E[d]
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a natural number, and write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Consider the structure morphism `projModelStrCR` of the projective model of the base change of $W$ to $R$, namely $\operatorname{Proj}$ of the quotient grading attached to the homogeneous Weierstrass cubic, mapped to $\operatorname{Spec} R$. Assume given: a relative group law $G$ on this model, i.e. multiplication, unit and inverse operations on the sets $\{\varphi : T \to \operatorname{Proj} \mid \varphi$ followed by the structure morphism equals $t\}$ for every $t : T \to \operatorname{Spec} R$, satisfying associativity, the two unit laws, left inverses and compatibility with base change along morphisms $T' \to T$ over $\operatorname{Spec} R$; and a family `ev` of bijections, one for each field $F$ that is an $R$-algebra, from the relative points over $\operatorname{Spec}$ of the structure map $R \to F$ to the affine points of the $F$-base change of the curve; and the hypothesis `hev` that `ev` is a points-evaluation, i.e. each `ev F` carries $G$-multiplication to addition of affine points and carries the twist `galTwist` $\sigma$ (precomposition with $\operatorname{Spec}$ of $\sigma$) to `Point.map` of $\sigma$, for every $R$-algebra automorphism $\sigma$ of $F$. Then for every natural number $d$ there is a bijection $e$ from the $d$-torsion subset $\{x \mid d \cdot x = 1\}$ of the relative points over $\operatorname{Spec} \overline{\mathbb{Q}}$ onto the $d$-torsion submodule `Submodule.torsionBy ℤ … (d : ℤ)` of the group of $\overline{\mathbb{Q}}$-points of $W$ viewed over $\mathbb{Q}$, such that (i) for all $x, y$ in that torsion subset and any proof that their $G$-product again lies in it, $e$ of the product is $e x + e y$, and (ii) for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$, every $x$ in the torsion subset and any proof that `galTwist` of $x$ by the restriction of $\sigma$ to an $R$-algebra automorphism lies in it, $e$ of that twist equals $\sigma \bullet e x$ for the Galois action on torsion points. No primality of $p$ and no positivity of $d$ are assumed.
--
--   This transports the scheme-theoretic $d$-torsion of a functorial group law on the projective Weierstrass model over $\mathbb{Z}_{(p)}$ to the classical $d$-torsion subgroup $E[d](\overline{\mathbb{Q}})$ of the affine model, as a Galois-equivariant additive bijection. It is used in the construction of a finite flat Hopf-algebra model of the $p$-power torsion at a good prime, via [`WeierstrassCurve.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor`](thm.html#WeierstrassCurve.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_galoisEquivariant.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel
open WeierstrassCurve
open scoped WeierstrassCurve.Affine

theorem WeierstrassProjModel.exists_torsionSubset_equiv_torsionBy_galoisEquivariant
    (W : WeierstrassCurve ℤ) (p : ℕ)
    (G : RelativeGroupLaw (GaloisRep.ratLocalizedAt p)
      (projModelStrCR (W.map (algebraMap ℤ (GaloisRep.ratLocalizedAt p))).toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra (GaloisRep.ratLocalizedAt p) F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (GaloisRep.ratLocalizedAt p) F)))
          (projModelStrCR (W.map (algebraMap ℤ (GaloisRep.ratLocalizedAt p))).toProjective) ≃
        ((W.map (algebraMap ℤ (GaloisRep.ratLocalizedAt p))).toProjective.baseChange
            F).toAffine.Point)
    (hev : IsPointsEval (W.map (algebraMap ℤ (GaloisRep.ratLocalizedAt p))).toProjective G ev)
    (d : ℕ) :
    ∃ e : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d) ≃
        ↥(Submodule.torsionBy ℤ
            ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (d : ℤ)),
      (∀ (x y : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d))
          (hxy : G.mul (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) x.1 y.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d),
          e ⟨_, hxy⟩ = e x + e y) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d))
        (hx : galTwist (σ.restrictScalars (GaloisRep.ratLocalizedAt p)) x.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d),
        e ⟨_, hx⟩ = σ • e x := by sorry
