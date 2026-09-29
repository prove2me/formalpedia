-- Prove2me | Theorems.Thm_WeierstrassProjModel_mul_comm_of_isPointsEval
-- name    : WeierstrassProjModel.mul_comm_of_isPointsEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/c2e0d948-4e44-5279-a78b-852320130a0e
-- title:
--   Commutativity of a relative group law with additive point evaluation
-- statement:
--   Let $K$ be a field and $W$ a Weierstrass curve over $K$ which is elliptic, and write $\pi :=$ `projModelStrCR W.toProjective` for the structure morphism to $\operatorname{Spec} K$ of the projective model of $W$, namely $\operatorname{Proj}$ of the graded quotient of the polynomial ring in three variables by the homogeneous Weierstrass ideal, mapped to $\operatorname{Spec} K$ through `Proj.toSpecZero` followed by the map induced on spectra by the degree-zero part. Let $G$ be a relative group law for $\pi$: for every scheme $T$ and every $t : T \to \operatorname{Spec} K$ it equips the set of morphisms $\varphi : T \to \operatorname{Proj}$ with $\varphi$ followed by $\pi$ equal to $t$ with a multiplication, a unit and an inversion satisfying associativity, both unit laws and left inverses, and compatible with composition: precomposing a product with $\psi : T' \to T$ satisfying $\psi$ followed by $t$ equal to $t'$ gives the product of the precompositions. Let $ev$ assign to each field $F$ that is a $K$-algebra a bijection between the points of $\pi$ over $\operatorname{Spec}$ of the structure map $K \to F$ and the affine points of $(W.\mathrm{toProjective}).\mathrm{baseChange}\,F$, and assume `IsPointsEval`: each $ev\,F$ carries $G$'s multiplication to addition of affine points, and intertwines the twist of a point by $\sigma : F \simeq_{\mathrm{alg}[K]} F$ with `Point.map` along $\sigma$. Then for every scheme $T$, every $t : T \to \operatorname{Spec} K$ and all points $x, y$ of $\pi$ over $t$, $G.\mathrm{mul}\,t\,x\,y = G.\mathrm{mul}\,t\,y\,x$.
--
--   This is the commutativity of the group law on the projective Weierstrass model, transferred from the classical commutativity of addition on the affine points of the base-changed curve to arbitrary $T$-valued points. It is used in the construction of relative group laws on quaternionic Shimura-type models, where commutativity of the fibrewise addition is needed before further structure (actions of maximal orders, smoothness of relative dimension one) is analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_mul_comm_of_isPointsEval.lean

import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.mul_comm_of_isPointsEval
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (G : RelativeGroupLaw K (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (projModelStrCR W.toProjective)) :
    G.mul t x y = G.mul t y x := by sorry
