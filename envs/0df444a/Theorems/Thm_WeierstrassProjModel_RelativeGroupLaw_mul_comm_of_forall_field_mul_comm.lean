-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_comm_of_forall_field_mul_comm
-- name    : WeierstrassProjModel.RelativeGroupLaw.mul_comm_of_forall_field_mul_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/12f8e7dc-111d-5fe2-a717-b68a394a063e
-- title:
--   Commutativity of a relative group law on an elliptic Weierstrass model
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ whose associated affine curve is elliptic. Write $E \to \operatorname{Spec} R$ for the structure morphism `projModelStrCR V`, namely $\operatorname{Proj}$ of the quotient grading attached to $V$ mapping to $\operatorname{Spec}$ of its degree-zero part and then to $\operatorname{Spec} R$. Assume: (i) for every field $K$ in the same universe carrying an $R$-algebra structure, the pullback of $E \to \operatorname{Spec} R$ along $\operatorname{Spec}$ of $R \to K$ is isomorphic, as a scheme, to the projective model `projModelCR` of the base change $V_K$; and (ii) $G$ is a relative group law on $E \to \operatorname{Spec} R$, i.e. for each scheme $T$ and each $t \colon T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set of $T$-morphisms $\varphi \colon T \to E$ with $\varphi$ followed by the structure morphism equal to $t$, satisfying associativity, both unit laws, the left inverse law, and naturality under precomposition with $\psi \colon T' \to T$ satisfying $\psi$ followed by $t$ equal to $t'$; and (iii) for every such field $K$ the multiplication of $G$ at the base point $\operatorname{Spec} K \to \operatorname{Spec} R$ is commutative. Then for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$ and all $x, y$ over $t$, $G.\mathrm{mul}\, t\, x\, y = G.\mathrm{mul}\, t\, y\, x$.
--
--   This is the rigidity step showing that a group law on a proper, flat, geometrically integral scheme over a base is commutative, specialised to the projective Weierstrass model of an elliptic curve over a commutative ring. It feeds the statement [`WeierstrassProjModel.RelativeGroupLaw.isCommutative_of_isElliptic_of_baseChangeIso`](thm.html#WeierstrassProjModel.RelativeGroupLaw.isCommutative_of_isElliptic_of_baseChangeIso) used in the construction of the group structure on good-reduction models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_mul_comm_of_forall_field_mul_comm.lean

import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.RelativeGroupLaw.mul_comm_of_forall_field_mul_comm
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (hcomm : ∀ (K : Type u) [Field K] [Algebra R K]
        (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) (projModelStrCR V)),
      G.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q
        = G.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) Q P) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)),
      G.mul t x y = G.mul t y x := by sorry
