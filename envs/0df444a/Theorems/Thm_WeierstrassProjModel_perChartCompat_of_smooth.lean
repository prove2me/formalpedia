-- Prove2me | Theorems.Thm_WeierstrassProjModel_perChartCompat_of_smooth
-- name    : WeierstrassProjModel.perChartCompat_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/6258d1b9-5b89-5f08-a33f-dcf2a3fb4108
-- title:
--   Per-chart compatibility of the six addition loci
-- statement:
--   Let $R$ be a Noetherian commutative integral domain and let $W$ be a Weierstrass curve over $R$. Write $E = \mathrm{Proj}$ of the graded quotient of the homogeneous polynomial ring in three variables by the homogeneous ideal of $W$'s projective model, and let $\pi$ denote the structure morphism `projModelStrCR W.toProjective`, namely $E \to \operatorname{Spec}$ of the degree-zero part followed by the map induced by $R \to (\text{degree-zero part})$. Assume: $\pi$ is `Smooth` (`hsm`), $\pi$ is `GeometricallyIntegral` (`hgi`), and the discriminant $W.\Delta$ is a unit in $R$ (`hΔ`). The conclusion is the predicate `KwLRPerChartCompat W`: for all $i, j \in \{0,1,2\}$ and all $l, l'$ in $\mathrm{Fin}\,3 \sqcup \mathrm{Fin}\,3$, writing $\mathcal{A}_i$ for the homogeneous localisation of the model away from the image of $X_i$ and $u_l =$ `kw_lrSixU W i j l` $\in \mathcal{A}_i \otimes_R \mathcal{A}_j$, the two morphisms $\operatorname{Spec}\bigl((\mathcal{A}_i \otimes_R \mathcal{A}_j)[1/u_l]\bigr) \to E$ and $\operatorname{Spec}\bigl((\mathcal{A}_i \otimes_R \mathcal{A}_j)[1/u_{l'}]\bigr) \to E$ given by `kw_lrSixU_toE W i j l` and `kw_lrSixU_toE W i j l'` (each the map induced by a chart or symmetric-chart algebra homomorphism followed by `Proj.awayι`) become equal after composing with the first, respectively second, projection of the pullback of the two localisation morphisms `kw_lrSixU_locMap W i j l` and `kw_lrSixU_locMap W i j l'` over $\operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)$.
--
--   This is the agreement, on overlaps inside a single product chart $\operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)$ of $E \times_R E$, of the six locally defined chord-and-tangent addition morphisms attached to the addition formulae, the compatibility needed before the local pieces can be glued. It is used by [`WeierstrassProjModel.addMorphism_gluing`](thm.html#WeierstrassProjModel.addMorphism_gluing) and by [`WeierstrassProjModel.exists_perChart_addMorphism_of_thirdLaw_nineCoverage`](thm.html#WeierstrassProjModel.exists_perChart_addMorphism_of_thirdLaw_nineCoverage); the proof cites [`WeierstrassProjModel.kw_a2_sixU_class_eq_addMap_of_delta_ne_zero`](thm.html#WeierstrassProjModel.kw_a2_sixU_class_eq_addMap_of_delta_ne_zero) and [`WeierstrassProjModel.sixU_toE_over`](thm.html#WeierstrassProjModel.sixU_toE_over).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_perChartCompat_of_smooth.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.perChartCompat_of_smooth.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    KwLRPerChartCompat W := by sorry
