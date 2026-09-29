-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrChart_gen_ne_zero
-- name    : WeierstrassProjModel.kw_lrChart_gen_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/cd8210ff-d98a-5ee9-919a-81d8e229812b
-- title:
--   Chart generators X_m/Xᵢ are nonzero on the projective Weierstrass model
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and Noetherian, and let $W$ be a Weierstrass curve over $R$ satisfying `W.IsElliptic`. Write $P =$ `W.toProjective.polynomial` for the homogeneous Weierstrass cubic in $R[X_0,X_1,X_2]$, let $I = \langle P\rangle$ be the homogeneous ideal `projModelHomogeneousIdealCR W.toProjective` it spans, and grade the quotient $R[X_0,X_1,X_2]/I$ by the submodules `projModelGradingCR W.toProjective` obtained as the images of the homogeneous components under the quotient map. For an index $i \in \{0,1,2\}$, let $\mathcal A_i$ denote the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of this graded ring at the image $\bar X_i$ of $X_i$. Then for all indices $i, m \in \{0,1,2\}$ the element `kw_lrChart_gen W i m`, namely the class of the fraction with numerator $\bar X_m$ and denominator $\bar X_i$, both taken in grading degree $1$, with denominator exhibited as $\bar X_i^{\,1}$, is nonzero in $\mathcal A_i$.
--
--   This is the statement that the standard affine coordinate $X_m/X_i$ does not vanish identically on the $i$-th standard chart of the projective Weierstrass model; in particular each chart ring is nontrivial. It is used in the verification of the group law on the projective model, where nonvanishing of chart generators is needed in the $y$-chart computations and in the comparison of generators across a tensor product of two charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrChart_gen_ne_zero.lean

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

theorem WeierstrassProjModel.kw_lrChart_gen_ne_zero
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i m : Fin 3) :
    kw_lrChart_gen W i m ≠ 0 := by sorry
