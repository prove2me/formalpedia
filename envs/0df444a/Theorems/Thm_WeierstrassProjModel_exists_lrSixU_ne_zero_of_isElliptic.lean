-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_of_isElliptic
-- name    : WeierstrassProjModel.exists_lrSixU_ne_zero_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/2203d2c7-a19e-57ed-a41c-c37afb9f3a6f
-- title:
--   Nondegeneracy of the six Lange–Ruppert elements on every chart pair
-- statement:
--   Let $R$ be a commutative ring that is an integral domain and Noetherian, and let $W$ be a Weierstrass curve over $R$ satisfying `W.IsElliptic`. Write $\mathcal A_i$, for $i \in \mathrm{Fin}\,3$, for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)/(F)$, where $F$ is the Weierstrass cubic of the associated projective model `W.toProjective` and the grading `projModelGradingCR` is the image grading `quotGradingSubmodule` obtained by pushing the homogeneous submodules of $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)$ along the quotient map, at the class of the coordinate $X_i$; each $\mathcal A_i$ is an $R$-algebra through the degree-zero part, as in `kw_pbac_awayAlgebra`. For indices $i,j \in \mathrm{Fin}\,3$ the family `kw_lrSixU W i j`, defined on $\mathrm{Fin}\,3 \sqcup \mathrm{Fin}\,3$ as the case split of `kw_lrChart_u W i j` on the left summand and `kw_lrSymChart_u W i j` on the right, takes values in $\mathcal A_i \otimes_R \mathcal A_j$; its members are the chart evaluations `kw_lrChart_ev'` of the classes of the vectors `kw_lrAdd_vec W k` and `kw_lrSym_vec W k`. The theorem asserts that for all $i,j$ there is an index $l$ with `kw_lrSixU W i j l` $\neq 0$ in $\mathcal A_i \otimes_R \mathcal A_j$.
--
--   This is the nondegeneracy input for the Lange–Ruppert pair of addition laws on the projective model: on each of the nine chart products of $E \times_R E$ at least one of the six coordinate expressions coming from the two addition laws is nonzero, so that the open locus where the laws are defined is nonempty, hence dense in an integral chart. It feeds the construction of the addition morphism chart by chart and the comparison statements for point classes and generic-point agreement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_of_isElliptic.lean

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

theorem WeierstrassProjModel.exists_lrSixU_ne_zero_of_isElliptic
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    ∃ l, kw_lrSixU W i j l ≠ 0 := by sorry
