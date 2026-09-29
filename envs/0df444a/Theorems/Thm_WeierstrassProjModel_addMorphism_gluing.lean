-- Prove2me | Theorems.Thm_WeierstrassProjModel_addMorphism_gluing
-- name    : WeierstrassProjModel.addMorphism_gluing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/24d06a0a-ecb5-51a4-be04-054729bce907
-- title:
--   Gluing data for the projective Weierstrass addition morphism
-- statement:
--   Let $R$ be a Noetherian integral domain in which $2$ is invertible, and let $W$ be a Weierstrass curve over $R$. Write $E = \mathrm{Proj}$ of the graded ring `projModelGradingCR W.toProjective` (the quotient of the homogeneous coordinate ring of $\mathbb{P}^2_R$ by the homogeneous ideal of the Weierstrass cubic of $W$), and let $\pi =$ `projModelStrCR W.toProjective` be its structure morphism to $\mathrm{Spec}\,R$, namely `Proj.toSpecZero` followed by the map induced by $R \to$ (degree-$0$ part). Assume $\pi$ is smooth, that $\pi$ is geometrically integral, and that the discriminant $W.\Delta$ is a unit. The conclusion is the conjunction of three statements. First, `KwLRSixUCoverage W`: for all $i, j \in \{0,1,2\}$ the six elements $\mathrm{kw\_lrSixU}\,W\,i\,j$ — the three dehomogenised coordinates `kw_lrChart_u` of the chord law together with the three coordinates `kw_lrSymChart_u` of the symmetric law, assembled over $\mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$ — span the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$, where $\mathcal{A}_i$ is the ring attached to the $i$-th standard chart of the projective model. Second, `KwLRPerChartCompat W`: for all $i, j$ and all $l, l'$ among those six indices, the morphisms `kw_lrSixU_toE` from the localisations away from the corresponding elements into $E$ agree after composition with the two projections of the pullback of the localisation maps $\mathrm{Spec}$ of those localisations $\to \mathrm{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)$. Third, `KwLROuterCompat W`: for any such coverage and per-chart compatibility data and all pairs $ij, ij' \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$, the glued chart morphisms `kw_lrOuter_toE` agree on the pullback of the two corresponding members of the open cover `kwProjPullbackOpenCoverCR` of $E \times_{\mathrm{Spec}\,R} E$ obtained from the standard affine cover of $E$ in each factor.
--
--   These are exactly the descent data needed to glue the chord and symmetric addition laws on the nine charts of $E \times_{\mathrm{Spec}\,R} E$ into a single addition morphism, in the style of complete systems of addition laws for elliptic curves. The result is used by [`WeierstrassProjModel.relativeGroupLaw_exists`](thm.html#WeierstrassProjModel.relativeGroupLaw_exists) to produce the relative group law on the projective Weierstrass model with all hypotheses discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_addMorphism_gluing.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_gluing.{u} {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Invertible (2 : R)] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    KwLRSixUCoverage W ∧ KwLRPerChartCompat W ∧ KwLROuterCompat W := by sorry
