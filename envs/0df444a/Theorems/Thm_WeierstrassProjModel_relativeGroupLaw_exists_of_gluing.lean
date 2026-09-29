-- Prove2me | Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing
-- name    : WeierstrassProjModel.relativeGroupLaw_exists_of_gluing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/906b89a6-9494-5c7a-9fc0-716e3d24cef5
-- title:
--   Relative group law on the projective Weierstrass model
-- statement:
--   Let $R$ be a Noetherian integral domain and $W$ a Weierstrass curve over $R$, and write $\pi =$ `projModelStrCR W.toProjective` for the structure morphism $\operatorname{Proj}(\mathcal{A}) \to \operatorname{Spec} R$ of the projective model of $W$, where $\mathcal{A}$ is the graded quotient of the homogeneous coordinate ring by the homogeneous ideal of the Weierstrass cubic. Assume $\pi$ is smooth and geometrically integral, that the discriminant $W.\Delta$ is a unit in $R$, and that the three gluing hypotheses hold: `KwLRSixUCoverage`, that for each pair $(i,j)$ of indices in $\mathrm{Fin}\,3$ the six elements $\mathrm{kw\_lrSixU}\,W\,i\,j$ generate the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$; `KwLRPerChartCompat`, that for each $(i,j)$ the six morphisms to the model defined on the away-localisations at those elements agree after pulling back any two of the corresponding localisation maps to $\operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)$; and `KwLROuterCompat`, that the nine chart morphisms $\mathrm{kw\_lrOuter\_toE}$ agree on all overlaps of the open cover `kwProjPullbackOpenCoverCR` of $\operatorname{Proj}(\mathcal{A}) \times_{\operatorname{Spec} R} \operatorname{Proj}(\mathcal{A})$ obtained from the affine chart cover on the left and on the right. The conclusion asserts the existence of a term $G$ of `RelativeGroupLaw R` $\pi$, that is: operations assigning to every scheme $T$ and every $t : T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set of $\varphi : T \to \operatorname{Proj}(\mathcal{A})$ with $\varphi$ followed by $\pi$ equal to $t$, subject to associativity, the two unit laws, left inversion, and naturality of the multiplication under precomposition with any $\psi : T' \to T$ satisfying $\psi$ followed by $t$ equal to $t'$; moreover $G$ is required to satisfy three further conditions: for all $T$, $t$ and points $x, y$, the morphism underlying $G.\mathrm{mul}\,t\,x\,y$ is the pullback lift of $x$ and $y$ followed by `kw_lrAddMorphism W hcov hcompat houter`; the morphism underlying $G.\mathrm{one}\,t$ is $t$ followed by the zero section `kwZeroSect R W`; and $G.\mathrm{mul}\,t$ is commutative.
--
--   This packages the glued addition morphism of the projective Weierstrass model, together with the zero section and the negation morphism, into a functorial abelian group structure on the $T$-valued points of the model over $\operatorname{Spec} R$, the relative group law of the elliptic curve $\operatorname{Proj}(\mathcal{A}) \to \operatorname{Spec} R$. It is the form in which the group law is consumed by [`WeierstrassProjModel.relativeGroupLaw_exists`](thm.html#WeierstrassProjModel.relativeGroupLaw_exists), where the gluing hypotheses are discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.relativeGroupLaw_exists_of_gluing.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    ∃ G : WeierstrassProjModel.RelativeGroupLaw R (projModelStrCR W.toProjective),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
          (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ kw_lrAddMorphism W hcov hcompat houter) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 = t ≫ (kwZeroSect R W).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)), G.mul t x y = G.mul t y x) := by sorry
