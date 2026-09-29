-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/473e1938-1135-59c7-958e-bb02c6f5b809
-- title:
--   Transport of the origin parameter under a change of variables
-- statement:
--   Let $T$ be a local ring that is complete and separated for the $\mathfrak m$-adic topology, $\mathfrak m = \mathrm{maximalIdeal}\,T$, let $W$ be a Weierstrass curve over $T$ and $C$ a Weierstrass change of variables $(u,r,s,t)$ over $T$. Let $\varphi$ be a graded ring homomorphism from the graded coordinate ring of the projective model of $W$ to that of $C \bullet W$, with the irrelevant ideal of the target contained in the image under $\varphi$ of the irrelevant ideal of the source (so that $\varphi$ induces a morphism `Proj.map φ hφ` of the projective models), and assume `IsVariableChangeHom W C φ`: $\varphi$ fixes the classes of constants, and sends the classes of $X_0, X_1, X_2$ to the classes of $u^2X_0 + rX_2$, $u^3X_1 + u^2sX_0 + tX_2$ and $X_2$ respectively. Let $P$ be a section of the projective model of $W$ over $\mathrm{Spec}\,T$ and $\chi$ a ring homomorphism from the origin chart ring of $W$ (the degree-zero homogeneous localisation away from the coordinate `coord W 1`) to $T$ such that $\chi$ is an origin-chart presentation of $P$ with both the origin parameter $\mathrm{originParam}\,\chi = -\chi(\mathrm{xOverY}\,W)$ and $\mathrm{originW}\,\chi$ in $\mathfrak m$. Let finally $P'$ be a section of the projective model of $C \bullet W$ whose underlying morphism followed by `Proj.map φ hφ` is the underlying morphism of $P$. Then there is a ring homomorphism $\chi'$ from the origin chart ring of $C \bullet W$ to $T$ which is an origin-chart presentation of $P'$ with $\mathrm{originParam}\,\chi'$ and $\mathrm{originW}\,\chi'$ in $\mathfrak m$, and whose origin parameter is obtained from that of $\chi$ by substitution into the change-of-variables power series, $\mathrm{originParam}\,\chi' = \big(u\,(X - r\,W.\mathrm{formalW})\cdot(\text{inverse of } W.\mathrm{variableChangeDenom}\,C)\big)(\mathrm{originParam}\,\chi)$, the substitution being the $\mathfrak m$-adically convergent evaluation [`FormalGroup.evalSeries`](def/FormalGroup_NSeries.html#L85).
--
--   This is the compatibility, in Weierstrass coordinates, between a change of variables on a curve over a complete local ring and the formal parameter at the origin: the parameter of a section transforms by the change-of-variables power series, as in the formal-group computations underlying Serre–Tate theory and the Katz–Mazur treatment of Drinfeld level structures. It is used by the level-moduli package lemmas that compare origin parameters of transported points with $u^{-1}$-scalings modulo $\mathfrak m^2$ and that identify level transports with actions of changes of variables.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hvc : IsVariableChangeHom W C φ)
    (P : Section W) (χ : OriginChartRing W →+* T) (hP : ReducesToOrigin P χ (maximalIdeal T))
    (P' : Section (C • W)) (hP' : P'.1 ≫ Proj.map φ hφ = P.1) :
    ∃ χ' : OriginChartRing (C • W) →+* T,
      ReducesToOrigin P' χ' (maximalIdeal T) ∧
      originParam χ' =
        (letI : WithIdeal T := ⟨maximalIdeal T⟩; FormalGroup.evalSeries (W.variableChangeSeries C) (originParam χ)) := by sorry
