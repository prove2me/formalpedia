-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/1d447b64-126a-5680-b8b2-a1196e88880a
-- title:
--   Lifting an origin-chart point through Proj of a coefficient homomorphism
-- statement:
--   Let $T,T'$ be commutative rings in one universe, let $W$ be a Weierstrass curve over $T$ in projective form, and let $f : T \to T'$ be a ring homomorphism, so that $W.\mathrm{map}\,f$ is the base-changed curve over $T'$. Write $\mathrm{projModelGradingCR}$ for the grading of the quotient $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,3)\,T / (W.\mathrm{polynomial})$ obtained by pushing forward the homogeneous submodules of the polynomial ring. Let $\varphi$ be a graded ring homomorphism from $\mathrm{projModelGradingCR}\,W$ to $\mathrm{projModelGradingCR}\,(W.\mathrm{map}\,f)$ satisfying the hypothesis `hφ` that the irrelevant ideal of the target is contained in the image under $\varphi$ of the irrelevant ideal of the source (the condition making `Proj.map φ hφ` available), and assume `IsCoefficientHom W f φ`, i.e. $\varphi$ carries the class of a constant $C\,a$ to the class of $C\,(f\,a)$ for every $a \in T$, and the class of $X_i$ to the class of $X_i$ for each $i \in \mathrm{Fin}\,3$. Let $B$ be a commutative ring and let $\chi'$ be a ring homomorphism from $\mathrm{OriginChartRing}\,(W.\mathrm{map}\,f)$, the degree-zero homogeneous localisation away from the class of the coordinate $X_1$, to $B$. The assertion is that there is a ring homomorphism $\chi$ from $\mathrm{OriginChartRing}\,W$ to $B$ such that $\mathrm{Spec}\,\chi'$ followed by $\mathrm{originChart}\iota\,(W.\mathrm{map}\,f)$ followed by $\mathrm{Proj.map}\,\varphi$ equals $\mathrm{Spec}\,\chi$ followed by $\mathrm{originChart}\iota\,W$; such that for every $t \in T$ the value of $\chi$ on the image of $t$ in degree zero agrees with the value of $\chi'$ on the image of $f\,t$ in degree zero; and such that $\chi(\mathrm{xOverY}\,W) = \chi'(\mathrm{xOverY}\,(W.\mathrm{map}\,f))$ and $\chi(\mathrm{zOverY}\,W) = \chi'(\mathrm{zOverY}\,(W.\mathrm{map}\,f))$, where these are the degree-zero fractions $X_0/X_1$ and $X_2/X_1$.
--
--   This is the chart-lifting step for the projective Weierstrass model: a $B$-point of the origin chart of the base-changed curve, composed with the morphism of $\mathrm{Proj}$'s induced by a homomorphism acting as $f$ on coefficients and identically on the three coordinates, factors through the origin chart of $W$ itself, with the affine coordinates $X/Y$, $Z/Y$ and the structural scalars transported accordingly. It is used in the comparison of the chart coordinates with Frobenius powers and in the construction of origin-chart points from formal-chart data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    {B : Type u} [CommRing B] (χ' : OriginChartRing (W.map f) →+* B) :
    ∃ χ : OriginChartRing W →+* B,
      Spec.map (CommRingCat.ofHom χ') ≫ originChartι (W.map f) ≫ Proj.map φ hφ =
        Spec.map (CommRingCat.ofHom χ) ≫ originChartι W ∧
      (∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
        χ' (fromZeroRingHom (projModelGradingCR (W.map f)) _ (algebraMap T' ((projModelGradingCR (W.map f)) 0) (f t)))) ∧
      χ (xOverY W) = χ' (xOverY (W.map f)) ∧ χ (zOverY W) = χ' (zOverY (W.map f)) := by sorry
