-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_idealSheafData_comap_eq_bot_iff_isDrinfeldBasisOver
-- name    : WeierstrassProjModel.RelativeGroupLaw.exists_idealSheafData_comap_eq_bot_iff_isDrinfeldBasisOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/b9516fd2-f863-52c6-a5a9-9ef8e4a87087
-- title:
--   Closedness of the relative Drinfeld-basis locus
-- statement:
--   Let $R$ be a commutative ring and $V$ a projective Weierstrass curve over $R$ whose affine model is elliptic, and write $f =$ `projModelStrCR V` for the structure morphism of its projective model, $\mathrm{Proj}$ of the graded quotient ring attached to $V$, over $\operatorname{Spec} R$. Let $G$ be a relative group law on $f$: for each scheme $T$ and each $t : T \to \operatorname{Spec} R$ a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the set of $T$-points of $f$ over $t$, that is on morphisms $T \to \mathrm{Proj}$ composing with $f$ to $t$, compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} R$. Let $ev$ be a family of bijections, one for every field $F$ that is an $R$-algebra, between the points of $f$ over $\operatorname{Spec} F \to \operatorname{Spec} R$ and the group of affine points of the base change $V_F$, and assume `IsPointsEval`: each $ev_F$ carries $G$'s multiplication to addition of points and commutes with the twist by any $R$-algebra automorphism $\sigma$ of $F$ and the induced map on points. Let $q$ be a positive natural number, $X$ a scheme, $t_0 : X \to \operatorname{Spec} R$, and $P_0, Q_0$ two points of $f$ over $t_0$. Then there exists a quasi-coherent ideal sheaf datum $J$ on $X$ such that for every scheme $T'$ and every morphism $u : T' \to X$, the pullback $J$ along $u$ is the zero ideal if and only if the pair $(u \circ P_0, u \circ Q_0)$, viewed as points over $u$ followed by $t_0$, satisfies `IsDrinfeldBasisOver` for $q$, i.e. the ideal `prodKerGraph` of the tuple `G.basisTupleOver` attached to $q$ and that pair — the product of the graph-kernel ideals of its members, on the pullback of $f$ along $u \circ t_0$ — coincides with the $q$-torsion ideal `torsionIdealOver`, the kernel ideal of the multiplication-by-$q$ morphism over the unit section, pulled back to that same scheme.
--
--   This is the representability statement that the relative Drinfeld-basis condition on a pair of sections is a closed condition on the base: the locus in $X$ over which $(P_0,Q_0)$ is a Drinfeld basis of the $q$-torsion is cut out by a single ideal sheaf, detected by vanishing of its pullback. It underlies the construction of the scheme of Drinfeld bases and is used in the global Drinfeld-basis criteria and in the finite-module representability result for $q \ge 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_exists_idealSheafData_comap_eq_bot_iff_isDrinfeldBasisOver.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.exists_idealSheafData_comap_eq_bot_iff_isDrinfeldBasisOver
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) (q : ℕ) (hq : 0 < q)
    {X : Scheme.{u}} (t₀ : X ⟶ Spec (CommRingCat.of R)) (P₀ Q₀ : SchemeHomOver t₀ (projModelStrCR V)) :
    ∃ J : X.IdealSheafData, ∀ {T' : Scheme.{u}} (u : T' ⟶ X),
      J.comap u = ⊥ ↔
        G.IsDrinfeldBasisOver q (u ≫ t₀) (schemeHomOverComp u rfl P₀) (schemeHomOverComp u rfl Q₀) := by sorry
