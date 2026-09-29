-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrThird_toE3_compat_of_isDomain
-- name    : WeierstrassProjModel.kw_lrThird_toE3_compat_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/1aae6d4b-5da1-532f-bb37-cb82317051d7
-- title:
--   Third-law chart agrees with chord/symmetric charts on overlaps
-- statement:
--   Let $R$ be a commutative ring that is an integral domain and Noetherian, and let $W$ be a Weierstrass curve over $R$ satisfying `W.IsElliptic`. Write $\mathcal A_i$ for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)/(\,W.\mathrm{toProjective}.\mathrm{polynomial}\,)$, graded by the images `quotGradingSubmodule` of the homogeneous submodules, at the class of the variable $X_i$; thus $\mathcal A_i$ is the coordinate ring of the $i$-th standard chart of the projective Weierstrass model of $W$, an $R$-algebra via `kw_pbac_awayAlgebra`. Fix $i,j,k \in \mathrm{Fin}\,3$ and $l \in \mathrm{Fin}\,3 \sqcup \mathrm{Fin}\,3$. Consider the two affine opens of $\operatorname{Spec}(\mathcal A_i \otimes_R \mathcal A_j)$ given by the localisation maps to $\mathrm{Localization.Away}$ of the element `kw_lrThird_u₃ W i j k` and, through `kw_lrSixU_locMap`, of the element `kw_lrSixU W i j l`, the latter being the chord coordinate `kw_lrChart_u W i j k'` when $l = \mathrm{inl}\,k'$ and the symmetric coordinate `kw_lrSymChart_u W i j k'` when $l = \mathrm{inr}\,k'$. The assertion is that on the fibre product of these two affine schemes over $\operatorname{Spec}(\mathcal A_i \otimes_R \mathcal A_j)$, the first projection followed by the third-law chart morphism `kw_lrThird_toE₃ W i j k` coincides with the second projection followed by `kw_lrSixU_toE W i j l`, the latter being $\operatorname{Spec}$ of the relevant chart homomorphism followed by the open immersion `Proj.awayι` into the projective model of $W$.
--
--   This is the compatibility half of the nine-chart description of the addition law on a projective Weierstrass model: the third addition law's chart morphisms glue with the six chord and symmetric chart morphisms on their pairwise overlaps over $E \times E$. It is used by [`WeierstrassProjModel.exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain`](thm.html#WeierstrassProjModel.exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain), which assembles the charts into a covering together with their agreement data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrThird_toE3_compat_of_isDomain.lean

import Definitions.Def_WeierstrassCurve_ProjModel_ThirdLawCharts
import Mathlib.RingTheory.Noetherian.Defs

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

theorem WeierstrassProjModel.kw_lrThird_toE3_compat_of_isDomain
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j k : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrThird_u₃ W i j k)))))
        (kw_lrSixU_locMap W i j l)
      ≫ kw_lrThird_toE₃ W i j k
    = pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrThird_u₃ W i j k)))))
        (kw_lrSixU_locMap W i j l)
      ≫ kw_lrSixU_toE W i j l := by sorry
