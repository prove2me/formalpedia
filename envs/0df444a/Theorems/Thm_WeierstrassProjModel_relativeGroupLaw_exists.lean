-- Prove2me | Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_exists
-- name    : WeierstrassProjModel.relativeGroupLaw_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/5b923706-c9f9-5aba-9975-1e27ab2931ff
-- title:
--   Existence of a commutative relative group law on the projective Weierstrass model
-- statement:
--   Let $R$ be a Noetherian integral domain in which $2$ is invertible, and let $W$ be a Weierstrass curve over $R$, with $E := \mathrm{Proj}$ of the graded quotient ring of its projective model and $\pi :=$ `projModelStrCR W.toProjective` the structure morphism to $\operatorname{Spec} R$. Assume $\pi$ is smooth and geometrically integral and that the discriminant $W.\Delta$ is a unit. Then there exist: proofs of the three gluing conditions, namely `KwLRSixUCoverage W` (for all $i,j \in \mathrm{Fin}\,3$, the six elements $\mathrm{kw\_lrSixU}\,W\,i\,j$ — the chord-chart and symmetric-chart data — span the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$), `KwLRPerChartCompat W` (for each $i,j$ and each pair $l,l'$ of the six indices, the two morphisms to $E$ defined on the localisations away from these elements agree after pullback along the localisation maps), and `KwLROuterCompat W` (the resulting per-chart morphisms on the chart-by-chart open cover of $E \times_{\operatorname{Spec} R} E$ agree on all pairwise pullbacks); and a `RelativeGroupLaw R` $\pi$, i.e. an operation on $T$-points over $\operatorname{Spec} R$ with unit, inverse, associativity, unit laws, left inverse law and naturality under base change $\psi$, such that for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and all $x,y$ with $x \circ \pi = t = y \circ \pi$: the morphism underlying $G.\mathrm{mul}\,t\,x\,y$ is the induced map $T \to E \times_{\operatorname{Spec} R} E$ followed by `kw_lrAddMorphism W hcov hcompat houter`, the morphism underlying $G.\mathrm{one}\,t$ is $t$ followed by the zero section `kwZeroSect R W`, and $G.\mathrm{mul}\,t\,x\,y = G.\mathrm{mul}\,t\,y\,x$.
--
--   This provides the relative (functor-of-points) commutative group structure on the projective Weierstrass model of an elliptic curve over a Noetherian domain with $2$ invertible, with the multiplication computed by the globally glued addition morphism and the identity by the standard zero section. It is used in the construction of finite flat Hopf-algebra models of torsion and in the identification of the group law with evaluation on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_relativeGroupLaw_exists.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.relativeGroupLaw_exists.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Invertible (2 : R)] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    ∃ (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)
      (G : WeierstrassProjModel.RelativeGroupLaw R (projModelStrCR W.toProjective)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
          (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ kw_lrAddMorphism W hcov hcompat houter) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 = t ≫ (kwZeroSect R W).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)), G.mul t x y = G.mul t y x) := by sorry
