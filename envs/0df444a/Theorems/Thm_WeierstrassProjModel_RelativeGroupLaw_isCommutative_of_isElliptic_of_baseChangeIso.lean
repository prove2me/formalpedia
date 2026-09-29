-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso
-- name    : WeierstrassProjModel.RelativeGroupLaw.isCommutative_of_isElliptic_of_baseChangeIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/c6b49b14-580e-535b-81cc-a6789b2d130f
-- title:
--   Relative group laws on the projective Weierstrass model are commutative
-- statement:
--   Let $R$ be a commutative ring (in a fixed universe) and let $V$ be a projective Weierstrass curve over $R$ whose associated affine Weierstrass curve satisfies `IsElliptic`. Write $E =$ `projModelCR V` for the `Proj` of the graded quotient ring `projModelGradingCR V` attached to $V$, with structure morphism `projModelStrCR V` $: E \to \operatorname{Spec} R$ obtained from `Proj.toSpecZero` followed by the map induced by $R \to$ (degree-zero part). Assume the base-change hypothesis $h_{\mathrm{bc}}$: for every field $K$ of the same universe equipped with an $R$-algebra structure, the fibre product of `projModelStrCR V` with $\operatorname{Spec}$ of $\operatorname{algebraMap} R K$ is isomorphic, as a scheme, to `projModelCR (V.baseChange K)`. Let $G$ be a relative group law on `projModelStrCR V`, i.e. an assignment, to each $R$-scheme $t : T \to \operatorname{Spec} R$, of multiplication, unit and inversion operations on the set of $T$-points $\{\varphi : T \to E \mid \varphi$ followed by the structure morphism equals $t\}$, satisfying associativity, the two unit laws, left inverses, and naturality of multiplication under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$. Then the multiplication of $G$ is commutative: for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and all $T$-points $x, y$, one has $G.\mathrm{mul}\,t\,x\,y = G.\mathrm{mul}\,t\,y\,x$.
--
--   This is the commutativity of an arbitrary group law on the projective Weierstrass model over an arbitrary commutative base ring, the relative analogue of the classical fact that a group law on a proper geometrically integral curve with a rational point is commutative. It feeds into the Drinfeld-style global torsion computations for Weierstrass curves, where the $T$-point group law must be known to be abelian over every base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso.lean

import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.RelativeGroupLaw.isCommutative_of_isElliptic_of_baseChangeIso
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)),
      G.mul t x y = G.mul t y x := by sorry
