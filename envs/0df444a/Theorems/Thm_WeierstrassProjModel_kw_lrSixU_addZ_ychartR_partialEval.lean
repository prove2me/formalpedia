-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrSixU_addZ_ychartR_partialEval
-- name    : WeierstrassProjModel.kw_lrSixU_addZ_ychartR_partialEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/ca951cb1-f0dc-508e-8f80-5b64a585ea96
-- title:
--   Partial evaluation of the chord Z-coordinate at [0:1:0]
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$. For $k \in \mathrm{Fin}\,3$ write $\mathcal A_k$ for the degree-zero homogeneous localization `HomogeneousLocalization.Away` of the graded ring $R[X_0,X_1,X_2]/(F)$, where $F$ is the Weierstrass cubic of `W.toProjective` and the grading is the image grading `quotGradingSubmodule` induced from the homogeneous-submodule grading of $R[X_0,X_1,X_2]$, at the class of $X_k$; each $\mathcal A_k$ is an $R$-algebra via the degree-zero part. Fix an index $i \in \mathrm{Fin}\,3$. The assertion is that there exists a ring homomorphism $\varphi \colon \mathcal A_i \otimes_R \mathcal A_1 \to \mathcal A_i$ such that $\varphi$ sends the element $\mathtt{kw\_lrSixU}\,W\,i\,1\,(\mathrm{inl}\,2)$, i.e. the value $\mathtt{kw\_lrChart\_u}\,W\,i\,1\,2$ obtained by applying `kw_lrChart_ev'` to the class of the third component of the chord addition vector `kw_lrAdd_vec` (the $Z$-component `kw_lrAdd_Z`), to $(\mathtt{kw\_lrChart\_gen}\,W\,i\,2)^2$, the square of the class of $X_2/X_i$ in $\mathcal A_i$. No condition on $W$ beyond being a Weierstrass curve over a commutative ring is imposed, and only the existence of one such $\varphi$ is asserted.
--
--   This is the computational step showing that the $Z$-component of the chord addition law on the projective Weierstrass model does not vanish identically: specialising the second factor to the point at infinity $[0:1:0]$ turns it into the square of the coordinate function $X_2/X_i$. It is used by [`WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartR`](thm.html#WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartR), which combines it with the non-vanishing of $X_2/X_i$ in a domain chart to conclude that the six-$U$ entry is nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrSixU_addZ_ychartR_partialEval.lean

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

theorem WeierstrassProjModel.kw_lrSixU_addZ_ychartR_partialEval (i : Fin 3) :
    ∃ (φ : ((𝒜 i) ⊗[R] (𝒜 1)) →+* (𝒜 i)),
      φ (kw_lrSixU W i 1 (.inl 2)) = (kw_lrChart_gen W i 2) ^ 2 := by sorry
