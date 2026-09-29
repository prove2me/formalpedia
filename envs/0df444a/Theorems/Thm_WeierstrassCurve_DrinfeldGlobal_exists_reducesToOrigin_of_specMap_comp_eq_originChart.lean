-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_of_specMap_comp_eq_originChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/7e12cafd-3aaa-54a8-be75-7a09655852e9
-- title:
--   Lifting an origin K-point to an origin chart section over a local ring
-- statement:
--   Let $T$ be a commutative local ring, $W$ a projective Weierstrass curve over $T$, and $P$ a section of the projective Weierstrass model, i.e. a morphism $P_1 : \operatorname{Spec} T \to \operatorname{Proj}$ of the graded coordinate ring of $W$ together with the datum that $P_1$ followed by the structure morphism `projModelStrCR W` is the identity of $\operatorname{Spec} T$. Let $K$ be a field and $\pi : T \to K$ a ring homomorphism whose kernel is exactly the maximal ideal of $T$, and let $\bar\chi : \mathcal{O}(D_+(Y)) \to K$ be a ring homomorphism from `OriginChartRing W`, the degree-zero part of the localisation of the graded model ring away from the coordinate $Y$. Assume that $\operatorname{Spec}(\pi)$ followed by $P_1$ coincides with $\operatorname{Spec}(\bar\chi)$ followed by the chart immersion `originChartι W`, and that $\bar\chi$ kills both chart coordinates $X/Y =$ `xOverY W` and $Z/Y =$ `zOverY W`. Then there exists a ring homomorphism $\chi : \mathcal{O}(D_+(Y)) \to T$ such that `ReducesToOrigin P χ (maximalIdeal T)` holds, that is: $P_1$ equals $\operatorname{Spec}(\chi)$ followed by `originChartι W`, and the two elements `originParam χ` and `originW χ` of $T$ (exhibited in the proof as the negatives of $\chi(X/Y)$ and $\chi(Z/Y)$) both lie in the maximal ideal of $T$; moreover $\pi \circ \chi = \bar\chi$.
--
--   This is the standard statement that a section of a projective Weierstrass model over a local ring whose reduction at the closed point is the origin lies entirely in the origin chart $D_+(Y)$, with affine coordinates in the maximal ideal. It supplies the entry hypothesis for the Drinfeld-basis criteria in the level moduli problems, and is cited by the existence statements for sections equivalent to Drinfeld bases at $\Gamma_0$-type and rigid-data level structures, as well as by a separation statement for points of the projective model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_of_specMap_comp_eq_originChart
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve.Projective T) (P : Section W)
    {K : Type u} [Field K] (π : T →+* K) (hπ : RingHom.ker π = maximalIdeal T)
    (χbar : OriginChartRing W →+* K)
    (h : Spec.map (CommRingCat.ofHom π) ≫ P.1 = Spec.map (CommRingCat.ofHom χbar) ≫ originChartι W)
    (hx : χbar (xOverY W) = 0) (hz : χbar (zOverY W) = 0) :
    ∃ χ : OriginChartRing W →+* T, ReducesToOrigin P χ (maximalIdeal T) ∧ π.comp χ = χbar := by sorry
