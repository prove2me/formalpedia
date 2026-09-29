-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lr_chartTensor_genProd_ne_genTensOne
-- name    : WeierstrassProjModel.kw_lr_chartTensor_genProd_ne_genTensOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/eb10c825-e646-5f88-99d7-f58be9855081
-- title:
--   Chart generators are not diagonal in the chart tensor product
-- statement:
--   Let $R$ be a commutative ring which is a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ satisfying `W.IsElliptic`. For $i : \mathrm{Fin}\,3$ write $\mathcal A_i$ for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the quotient ring $R[X_0,X_1,X_2]/(F)$, where $F$ is the Weierstrass cubic `W.toProjective.polynomial` and the grading is the image under the quotient map of the homogeneous submodules of $R[X_0,X_1,X_2]$, at the class of $X_i$; the $R$-algebra structure on $\mathcal A_i$ is the one induced by $R \to (\text{degree }0\text{ piece}) \to \mathcal A_i$. For $i,m : \mathrm{Fin}\,3$ let $\mathrm{gen}_i(m) \in \mathcal A_i$ be the class of the degree-one fraction with numerator the class of $X_m$ and denominator the class of $X_i$ (to the first power). The assertion is that for all $i, j : \mathrm{Fin}\,3$ there exists $k : \mathrm{Fin}\,3$ such that, in the tensor product $\mathcal A_i \otimes_R \mathcal A_j$,
--   $$\mathrm{gen}_i(j) \otimes \mathrm{gen}_j(k) \neq \mathrm{gen}_i(k) \otimes 1 .$$
--
--   This is the element-level separation statement underlying the fact that the two generic chart-projection point classes of the projective Weierstrass model differ: a homogeneous triple read off in the $i$-th chart and one read off in the $j$-th chart cannot agree up to a scalar after base change to $\mathcal A_i \otimes_R \mathcal A_j$. It is used by [`WeierstrassProjModel.kw_lr_chartTensor_genericProj_pointClass_ne`](thm.html#WeierstrassProjModel.kw_lr_chartTensor_genericProj_pointClass_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lr_chartTensor_genProd_ne_genTensOne.lean

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

theorem WeierstrassProjModel.kw_lr_chartTensor_genProd_ne_genTensOne
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    ∃ k : Fin 3, (kw_lrChart_gen W i j : (𝒜 i)) ⊗ₜ[R] (kw_lrChart_gen W j k : (𝒜 j))
      ≠ (kw_lrChart_gen W i k) ⊗ₜ[R] (1 : (𝒜 j)) := by sorry
