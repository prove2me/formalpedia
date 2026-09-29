-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_of_specMap_comp_eq_zChart
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_of_specMap_comp_eq_zChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/e6bd68c9-ed28-55cb-9899-90f0a4544ec8
-- title:
--   Lifting a K-point in the chart D₊(Z) to a section through an affine point
-- statement:
--   Let $T$ be a local ring, $W$ a projective Weierstrass cubic over $T$, and $S$ a section of the projective Weierstrass model of $W$, that is, a morphism $S.1$ from $\operatorname{Spec} T$ to $\operatorname{Proj}$ of the graded quotient ring `projModelGradingCR W` whose composite with the structure morphism `projModelStrCR W` is the identity. Let $K$ be a field, $\pi : T \to K$ a ring homomorphism whose kernel is exactly the maximal ideal of $T$, and $\rho bar : \mathtt{ZChartRing}\,W \to K$ a ring homomorphism, where $\mathtt{ZChartRing}\,W$ is the degree-zero homogeneous localisation of the model ring away from the class $Z$ of the third coordinate, i.e. the coordinate ring of the chart $D_+(Z)$. Assume that $\operatorname{Spec}(\pi)$ followed by $S.1$ equals $\operatorname{Spec}(\rho bar)$ followed by the chart morphism `zChartι W`. Then there exist $x, y \in T$ such that $S$ is the section through $(x,y)$ — there is a ring homomorphism $\chi : \mathtt{ZChartRing}\,W \to T$ with $S.1$ equal to $\operatorname{Spec}(\chi)$ followed by `zChartι W`, and $\chi(X/Z) = x$, $\chi(Y/Z) = y$ — and moreover $\pi x = \rho bar(X/Z)$ and $\pi y = \rho bar(Y/Z)$, where $X/Z$ and $Y/Z$ denote `xOverZ W` and `yOverZ W`.
--
--   This is the affine-chart form of the statement that a morphism from the spectrum of a local ring into a scheme factors through any open subscheme containing the image of the closed point: a section of the projective Weierstrass model whose reduction lands in the chart $D_+(Z)$ is itself the section through a pair of affine coordinates in $T$ reducing to the given ones. It is used in [`WeierstrassProjModel.exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq`](thm.html#WeierstrassProjModel.exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq) in the analysis of points of the model over local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_of_specMap_comp_eq_zChart.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_of_specMap_comp_eq_zChart
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve.Projective T) (S : Section W)
    {K : Type u} [Field K] (π : T →+* K) (hπ : RingHom.ker π = maximalIdeal T)
    (ρbar : ZChartRing W →+* K)
    (h : Spec.map (CommRingCat.ofHom π) ≫ S.1 = Spec.map (CommRingCat.ofHom ρbar) ≫ zChartι W) :
    ∃ x y : T, IsSectionThrough S x y ∧ π x = ρbar (xOverZ W) ∧ π y = ρbar (yOverZ W) := by sorry
