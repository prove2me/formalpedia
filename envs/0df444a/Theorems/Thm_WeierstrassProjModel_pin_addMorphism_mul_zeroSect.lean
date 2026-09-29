-- Prove2me | Theorems.Thm_WeierstrassProjModel_pin_addMorphism_mul_zeroSect
-- name    : WeierstrassProjModel.pin_addMorphism_mul_zeroSect
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/40b1549f-9703-51d1-8f2f-a68387ea5db4
-- title:
--   Right unit identity for a pinned addition morphism
-- statement:
--   Let $R$ be a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ which is elliptic. Write $E = \operatorname{Proj}$ of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(W_{\mathrm{proj}}\text{-polynomial})$, graded by the images of the homogeneous submodules, and let $\pi =$ `projModelStrCR W.toProjective` be its structure morphism to $\operatorname{Spec} R$, namely `Proj.toSpecZero` followed by the morphism of spectra induced by $R \to$ (degree-zero part). Let $m \colon E \times_{\operatorname{Spec} R} E \to E$ be a morphism such that $m$ followed by $\pi$ equals the first projection followed by $\pi$, and suppose $m$ is pinned in the following sense: for all $i, j \in \mathrm{Fin}\,3$ and all $l \in \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$, the composite of the localisation morphism `kw_lrSixU_locMap W i j l` from $\operatorname{Spec}$ of the localisation away from `kw_lrSixU W i j l` to $\operatorname{Spec}$ of $(\mathcal{A} i) \otimes_R (\mathcal{A} j)$, the inverse of the chart isomorphism identifying the $(i,j)$ member of the pullback open cover with that affine spectrum, the open immersion of that member, and $m$, equals `kw_lrSixU_toE W i j l`. Then the section $(\mathrm{id}_E, \pi \text{ followed by the zero section})$ of $E \times_{\operatorname{Spec} R} E$ over $E$, followed by $m$, is the identity of $E$.
--
--   This is the right unit axiom $x + O = x$ for a candidate relative group law on the projective Weierstrass model, in the form of an identity of morphisms of schemes over $\operatorname{Spec} R$, under the hypothesis that $m$ restricts on the Lange–Ruppert distinguished opens of the bi-chart covering to the prescribed addition morphisms. It is one of the identities used by [`WeierstrassProjModel.exists_relativeGroupLaw_mul_eq_one_eq_zeroSect_of_addMorphism_sixU_pin`](thm.html#WeierstrassProjModel.exists_relativeGroupLaw_mul_eq_one_eq_zeroSect_of_addMorphism_sixU_pin) and [`WeierstrassProjModel.relativeGroupLaw_nonempty_of_addMorphism_sixU_pin`](thm.html#WeierstrassProjModel.relativeGroupLaw_nonempty_of_addMorphism_sixU_pin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_pin_addMorphism_mul_zeroSect.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem WeierstrassProjModel.pin_addMorphism_mul_zeroSect
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (m : pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ⟶ projModelCR W.toProjective)
    (hm_over : m ≫ projModelStrCR W.toProjective
        = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective)
    (hmpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l
        ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j) ≫ m
      = kw_lrSixU_toE W i j l) :
    pullback.lift (𝟙 (projModelCR W.toProjective))
        (projModelStrCR W.toProjective ≫ (kwZeroSect R W).1)
        (by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id, Category.id_comp])
      ≫ m = 𝟙 (projModelCR W.toProjective) := by sorry
