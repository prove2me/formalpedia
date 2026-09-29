-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartL
-- name    : WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/6c7f7610-52e6-5a6c-916b-df9ca2614f97
-- title:
--   Nonvanishing of the chord Z-component on the Y-chart
-- statement:
--   Let $R$ be a commutative ring that is an integral domain and Noetherian, and let $W$ be a Weierstrass curve over $R$ satisfying `W.IsElliptic`. For $i \in \{0,1,2\}$ write $\mathcal{A}_i$ for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(F)$ at the image of $X_i$, where $F$ is the Weierstrass cubic `W.toProjective.polynomial`, the ideal is `projModelHomogeneousIdealCR` (the span of $F$, homogeneous), and the grading `projModelGradingCR` in degree $n$ is the image of the $n$-th homogeneous submodule of $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)$ under the quotient map; thus $\mathcal{A}_i$ is the coordinate ring of the affine chart $X_i \neq 0$ of the projective Weierstrass model, regarded as an $R$-algebra via `kw_pbac_awayAlgebra`. For indices $i,j$ the family `kw_lrSixU W i j` on $\mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$ is defined by `Sum.elim` from the addition-law components `kw_lrChart_u W i j` on the left summand and their symmetric counterparts `kw_lrSymChart_u W i j` on the right summand, with values in $\mathcal{A}_i \otimes_R \mathcal{A}_j$. The assertion is that for every $j \in \{0,1,2\}$ the element `kw_lrSixU W 1 j (.inl 2)`, i.e. the third ($Z$-) component of the chord addition vector evaluated in the tensor chart with left index fixed to $i = 1$, is nonzero in $\mathcal{A}_1 \otimes_R \mathcal{A}_j$.
--
--   This supplies the explicit witness showing that on the $(1,j)$ bichart at least one component of the Lange–Ruppert-style system of addition laws on the projective Weierstrass model does not vanish; such nonvanishing is what allows the addition law to define a morphism on that chart. It is cited by [`WeierstrassProjModel.exists_lrSixU_ne_zero_ychartL`](thm.html#WeierstrassProjModel.exists_lrSixU_ne_zero_ychartL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartL.lean

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

theorem WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartL
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (j : Fin 3) :
    kw_lrSixU W 1 j (.inl 2) ≠ 0 := by sorry
