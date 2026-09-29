-- Prove2me | Theorems.Thm_WeierstrassProjModel_mul_comm_of_isPointsEval_domain
-- name    : WeierstrassProjModel.mul_comm_of_isPointsEval_domain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/d9d1e8aa-b356-5f07-85e7-04118ea9e085
-- title:
--   Commutativity of a relative group law with additive points evaluation
-- statement:
--   Let $R$ be a Noetherian integral domain, let $W$ be a Weierstrass curve over $R$ which is elliptic, and write $\pi =$ `projModelStrCR W.toProjective` for the structure morphism to $\operatorname{Spec} R$ of the projective model of $W$, namely $\operatorname{Proj}$ of the graded quotient of the polynomial ring in three variables by the homogeneous ideal of the projective Weierstrass cubic, mapped to $\operatorname{Spec} R$ through $\operatorname{Proj}.\mathrm{toSpecZero}$ and the degree-zero part. Let $G$ be a relative group law for $\pi$: for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ it provides a multiplication, unit and inversion on the set of $\varphi : T \to \operatorname{Proj}$ with $\varphi$ followed by $\pi$ equal to $t$, satisfying associativity, the two unit laws and left inverse, and compatible with precomposition by morphisms $\psi$ of base schemes satisfying $t' = t \circ \psi$. Let `ev` assign to each field $F$ with an $R$-algebra structure a bijection from the points over $\operatorname{Spec}$ of $R \to F$ to the affine points of the base change of $W$ to $F$, and assume `IsPointsEval` for $W$, $G$ and `ev`: each `ev F` sends `G.mul` to addition of affine points, and intertwines the twist by an $R$-algebra automorphism $\sigma$ of $F$ with `Point.map` along $\sigma$. Then for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and all points $x, y$ over $t$, one has `G.mul t x y = G.mul t y x`.
--
--   This transports the commutativity of the group law on an elliptic curve, known on field-valued points through the affine chord–tangent addition, to the group law on arbitrary $T$-valued points of the projective model over the base, the passage resting on properness, smoothness and geometric integrality of the model and on integrality of the relevant fibre products. It is used in the construction of the finite free Hopf algebra of rank $p^2$ over the $p$-adic integers attached to the $p$-torsion of such a model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_mul_comm_of_isPointsEval_domain.lean

import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.mul_comm_of_isPointsEval_domain
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (_ : IsPointsEval W.toProjective G ev)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t (projModelStrCR W.toProjective)) : G.mul t x y = G.mul t y x := by sorry
