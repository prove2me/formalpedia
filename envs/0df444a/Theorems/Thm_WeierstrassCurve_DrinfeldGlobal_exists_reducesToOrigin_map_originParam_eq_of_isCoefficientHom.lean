-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c31a2b07-dbda-5ee1-a77d-2870187d93f8
-- title:
--   Origin-chart data transport along a coefficient homomorphism
-- statement:
--   Let $T$ and $T'$ be commutative rings, $W$ a Weierstrass curve over $T$, and $f : T \to T'$ a ring homomorphism. Let $\varphi$ be a graded ring homomorphism from the quotient grading `projModelGradingCR W` on $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,3)\,T$ modulo the span of the Weierstrass cubic of $W$ to the corresponding graded ring for $W.\mathrm{map}\,f$, and assume the irrelevant ideal of the target grading is contained in the image under $\varphi$ of the irrelevant ideal of the source, so that $\varphi$ induces `Proj.map φ hφ`. Assume `IsCoefficientHom W f φ`: $\varphi$ carries the class of a constant $C\,a$ to the class of $C\,(f\,a)$ for every $a \in T$, and fixes the classes of the coordinates $X_i$, $i \in \mathrm{Fin}\,3$. Let $P$ be a section of the projective model of $W$ over $\mathrm{Spec}\,T$, let $\chi$ be a ring homomorphism from the degree-zero homogeneous localisation `OriginChartRing W` at `coord W 1` to $T$, and let $I$ be an ideal of $T$ such that `ReducesToOrigin P χ I` holds, i.e. the predicate `IsOriginChartSection P χ` holds and both $\mathrm{originParam}\,\chi = -\chi(\mathtt{xOverY}\,W)$ and $\mathrm{originW}\,\chi = -\chi(\mathtt{zOverY}\,W)$ lie in $I$. Let $P'$ be a section for $W.\mathrm{map}\,f$ whose underlying morphism followed by `Proj.map φ hφ` equals $\mathrm{Spec}\,(f)$ followed by the underlying morphism of $P$. Then there exists a ring homomorphism $\chi' : \mathtt{OriginChartRing}\,(W.\mathrm{map}\,f) \to T'$ with `ReducesToOrigin P' χ' (I.map f)`, $\mathrm{originParam}\,\chi' = f(\mathrm{originParam}\,\chi)$ and $\mathrm{originW}\,\chi' = f(\mathrm{originW}\,\chi)$.
--
--   This is the base-change compatibility for sections through the origin of a Weierstrass projective model: an origin chart presentation of a section, together with its parameter and its $w$-coordinate, descends along any coefficient-preserving graded homomorphism and the corresponding map of Proj schemes, with the ideal of reduction replaced by its image. It is used in the comparison of level and moduli data on Weierstrass models, where origin parameters of sections have to be matched after changing the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (P : Section W) (χ : OriginChartRing W →+* T) (I : Ideal T) (hP : ReducesToOrigin P χ I)
    (P' : Section (W.map f))
    (hP' : P'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f) ≫ P.1) :
    ∃ χ' : OriginChartRing (W.map f) →+* T',
      ReducesToOrigin P' χ' (I.map f) ∧ originParam χ' = f (originParam χ) ∧ originW χ' = f (originW χ) := by sorry
