-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_of_addMorphism_sixU_pin
-- name    : WeierstrassProjModel.exists_isPointsEval_of_addMorphism_sixU_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/a36c8098-fd7f-5fb0-ac8a-62c83d9556f1
-- title:
--   Points evaluation for a law pinned to six addition laws
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$ whose discriminant $W.\Delta$ is a unit. Write $\pi \colon E \to \operatorname{Spec} R$ for `projModelStrCR W.toProjective`, the structure morphism of the projective model $E = \operatorname{Proj}$ of the graded quotient ring attached to the homogeneous Weierstrass cubic, and let $\mathcal A_i$ ($i \in \mathrm{Fin}\,3$) be the degree-one away algebras giving the standard affine charts, so that the charts of $E \times_{\operatorname{Spec} R} E$ are identified with $\operatorname{Spec}(\mathcal A_i \otimes_R \mathcal A_j)$ by `kwProjPullbackChartIsoCR`. Two data are assumed. First, a morphism $m \colon E \times_{\operatorname{Spec} R} E \to E$ which is pinned to the six distinguished addition-law loci: for all $i, j \in \mathrm{Fin}\,3$ and every $l \in \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$, the composite of the localisation morphism $\operatorname{Spec}\bigl(\text{Localization.Away}(\mathtt{kw\_lrSixU } W\, i\, j\, l)\bigr) \to \operatorname{Spec}(\mathcal A_i \otimes_R \mathcal A_j)$ with the inverse chart isomorphism, the inclusion of the $(i,j)$-chart into the pullback, and $m$, equals the morphism `kw_lrSixU_toE W i j l` into $E$. Second, a relative group law $G$ on $\pi$ — functorial multiplication, unit and inversion on $T$-points $\{\varphi \colon T \to E \mid \varphi \circ \pi = t\}$ satisfying associativity, unit laws, left inverses and compatibility with base change — whose multiplication is induced by $m$: for every $t \colon T \to \operatorname{Spec} R$ and all $T$-points $x, y$, the morphism underlying $G.\mathrm{mul}\, t\, x\, y$ is $\mathrm{lift}(x, y)$ followed by $m$. The conclusion is the existence of a family of bijections $\mathrm{ev}_F$, one for each field $F$ that is an $R$-algebra, between the $\operatorname{Spec} F$-points of $E$ over $\operatorname{Spec} R$ and the points of the affine Weierstrass curve $W \otimes_R F$, satisfying `IsPointsEval W.toProjective G ev`: each $\mathrm{ev}_F$ carries $G.\mathrm{mul}$ to addition of points, and for every $\sigma \in \operatorname{Aut}_R(F)$ it carries the twist of a point by $\operatorname{Spec}(\sigma)$ to the image of the corresponding affine point under $\sigma$.
--
--   This identifies the functorial group law on the projective Weierstrass model with the classical chord-and-tangent group law on affine points, compatibly with the action of $R$-automorphisms of the field of coefficients, assuming only that the multiplication agrees with the six Lange–Ruppert addition-law morphisms where these are defined (no hypothesis on the residue characteristic $2$). It is the step used by [`WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain`](thm.html#WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain) and its variant with the unit section, which construct such a group law together with its points evaluation for elliptic curves over a domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_isPointsEval_of_addMorphism_sixU_pin.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in

theorem WeierstrassProjModel.exists_isPointsEval_of_addMorphism_sixU_pin
    {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
    (m : pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ⟶ projModelCR W.toProjective)
    (hmpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l
        ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j) ≫ m
      = kw_lrSixU_toE W i j l)
    (G : RelativeGroupLaw R (projModelStrCR W.toProjective))
    (hGmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
          (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) :
    ∃ ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra R F],
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR W.toProjective) ≃
            (W.toProjective.baseChange F).toAffine.Point,
        IsPointsEval W.toProjective G ev := by sorry
