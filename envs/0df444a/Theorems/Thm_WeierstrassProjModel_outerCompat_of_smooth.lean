-- Prove2me | Theorems.Thm_WeierstrassProjModel_outerCompat_of_smooth
-- name    : WeierstrassProjModel.outerCompat_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/1a0b74a4-483e-50e5-96bc-118bb2477c78
-- title:
--   Outer gluing compatibility of the chart-wise addition morphisms
-- statement:
--   Let $R$ be a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$, with projective model $E = \mathrm{Proj}$ of the graded quotient of $R[X_0,X_1,X_2]$ by the homogeneous Weierstrass ideal and structure morphism `projModelStrCR W.toProjective` $: E \to \operatorname{Spec} R$ (the canonical map to $\operatorname{Spec}$ of the degree-zero part, composed with the map induced by $R \to \mathcal{A}_0$). Assume that this structure morphism satisfies the predicates `Smooth` and `GeometricallyIntegral`, and that the discriminant $W.\Delta$ is a unit in $R$. The conclusion is `KwLROuterCompat W`: for every proof `hcov` that for all $i,j \in \{0,1,2\}$ the six elements `kw_lrSixU W i j l` span the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$ (the tensor product of the two away-localisations at $X_i$, $X_j$), every proof `hcompat` of the per-chart compatibility (the morphisms `kw_lrSixU_toE W i j l` to $E$ agree after pullback along all pairs of the six locus maps `kw_lrSixU_locMap W i j l`), and every pair of chart indices $ij, ij' \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$, the two morphisms `kw_lrOuter_toE W hcov hcompat ij` and `kw_lrOuter_toE W hcov hcompat ij'` — each the chart isomorphism followed by the glued per-chart addition `kw_lrPerChart_toE` — agree after composing with the two projections of the pullback of the corresponding two members of the nine-chart open cover `kwProjPullbackOpenCoverCR` of $E \times_{\operatorname{Spec} R} E$.
--
--   This is the cocycle condition on the overlaps of the nine charts $E_i \times_R E_j$ of $E \times_R E$ which, together with the per-chart gluing, allows the chart-wise addition morphisms to be glued into a single addition morphism $E \times_R E \to E$; it is used by [`WeierstrassProjModel.addMorphism_gluing`](thm.html#WeierstrassProjModel.addMorphism_gluing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_outerCompat_of_smooth.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.outerCompat_of_smooth.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    KwLROuterCompat W := by sorry
