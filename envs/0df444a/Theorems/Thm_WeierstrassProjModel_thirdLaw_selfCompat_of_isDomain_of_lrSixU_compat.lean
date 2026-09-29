-- Prove2me | Theorems.Thm_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat
-- name    : WeierstrassProjModel.thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/3ef6cdea-55cc-537b-b5da-07cbd9c55b87
-- title:
--   Self-compatibility of the three charts over a domain
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$. For $i \in \{0,1,2\}$ write $\mathcal A_i$ for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the quotient ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(W_{\mathrm{proj}}.\mathrm{polynomial})$, graded by the images of the homogeneous submodules, at the image of the variable $X_i$; let $E =$ `projModelCR W.toProjective` be $\mathrm{Proj}$ of that graded quotient. Fix $i, j \in \{0,1,2\}$ and assume $\mathcal A_i \otimes_R \mathcal A_j$ is an integral domain. Assume further that at least one of the six elements $u_l =$ `kw_lrSixU W i j l`, $l \in \mathrm{Fin}\,3 \sqcup \mathrm{Fin}\,3$ (the three chart elements `kw_lrChart_u` and the three symmetric ones `kw_lrSymChart_u`), is nonzero in $\mathcal A_i \otimes_R \mathcal A_j$. Given three elements $u^{(3)}_k \in \mathcal A_i \otimes_R \mathcal A_j$ ($k \in \mathrm{Fin}\,3$) and morphisms $\tau_k \colon \mathrm{Spec}\,(\mathcal A_i \otimes_R \mathcal A_j)_{u^{(3)}_k} \to E$, suppose that for every $k$ and every $l$ the two projections of the pullback of $\mathrm{Spec}$ of the localisation map at $u^{(3)}_k$ against $\mathrm{Spec}$ of the localisation map at $u_l$ satisfy: the first projection followed by $\tau_k$ equals the second projection followed by `kw_lrSixU_toE W i j l`. Then for all $k, k'$ the first projection of the pullback of the two localisation maps at $u^{(3)}_k$ and $u^{(3)}_{k'}$ followed by $\tau_k$ equals the second projection followed by $\tau_{k'}$.
--
--   This is the compatibility of the three auxiliary addition charts with one another on their overlaps, deduced from their compatibility with the six Lange–Ruppert-type charts of the addition law on the projective Weierstrass model. It is the case of mutual agreement among the three charts used in the gluing argument of [`WeierstrassProjModel.exists_perChart_addMorphism_of_nineGlue_compat`](thm.html#WeierstrassProjModel.exists_perChart_addMorphism_of_nineGlue_compat), which assembles the per-chart morphisms into a single addition morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

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

theorem WeierstrassProjModel.thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat
    (i j : Fin 3) [IsDomain ((𝒜 i) ⊗[R] (𝒜 j))]
    (hne : ∃ l, kw_lrSixU W i j l ≠ 0)
    (u₃ : Fin 3 → (𝒜 i) ⊗[R] (𝒜 j))
    (toE₃ : ∀ k : Fin 3,
      Spec (CommRingCat.of (Localization.Away (u₃ k))) ⟶ projModelCR W.toProjective)
    (hcompat₃ : ∀ (k : Fin 3) (l : Fin 3 ⊕ Fin 3),
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
          (kw_lrSixU_locMap W i j l)
        ≫ toE₃ k
      = pullback.snd
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
          (kw_lrSixU_locMap W i j l)
        ≫ kw_lrSixU_toE W i j l)
    (k k' : Fin 3) :
    pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k')))))
      ≫ toE₃ k
    = pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k')))))
      ≫ toE₃ k' := by sorry
