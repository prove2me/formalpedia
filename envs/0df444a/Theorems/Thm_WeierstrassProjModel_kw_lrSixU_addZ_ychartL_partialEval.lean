-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval
-- name    : WeierstrassProjModel.kw_lrSixU_addZ_ychartL_partialEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/e111d8a8-577d-578b-a78c-fa8b9179b743
-- title:
--   Left Y-chart partial evaluation of the chord Z-coordinate
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$. For $i : \mathrm{Fin}\,3$ write $\mathcal A_i$ for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the quotient ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)/(F)$, where $F$ is the projective Weierstrass polynomial of $W$ and the grading is the image of the grading by homogeneous submodules under the quotient map, localised away from the class of the variable $X_i$; each $\mathcal A_i$ is an $R$-algebra through $R \to (\text{degree-}0\text{ part}) \to \mathcal A_i$. The assertion is: for every index $j : \mathrm{Fin}\,3$ there exists a ring homomorphism $\varphi \colon \mathcal A_1 \otimes_R \mathcal A_j \to \mathcal A_j$ such that $\varphi$ sends the element $\mathtt{kw\_lrSixU}\,W\,1\,j\,(\mathrm{inl}\,2)$ — that is, by the definition of `kw_lrSixU` as a `Sum.elim`, the left-hand (chord) entry $\mathtt{kw\_lrChart\_u}\,W\,1\,j\,2$, the image in $\mathcal A_1 \otimes_R \mathcal A_j$ of the third ($Z$-) component of the chord addition vector of $W$ — to $-(\mathtt{kw\_lrChart\_gen}\,W\,j\,2)^2$, where $\mathtt{kw\_lrChart\_gen}\,W\,j\,2 \in \mathcal A_j$ is the degree-zero fraction with numerator the class of $X_2$ and denominator the class of $X_j$, i.e. $X_2/X_j$. Only the existence of such a $\varphi$ is asserted, not a particular choice.
--
--   This is the evaluation of the $Z$-coordinate of the chord addition law at the point at infinity $[0:1:0]$ in the first factor, in the chart-by-chart formalism for the group law on the projective Weierstrass model. It is the computational step behind [`WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartL`](thm.html#WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartL), which records that this addition-law coordinate does not vanish identically.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval.lean

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

theorem WeierstrassProjModel.kw_lrSixU_addZ_ychartL_partialEval (j : Fin 3) :
    ∃ (φ : ((𝒜 1) ⊗[R] (𝒜 j)) →+* (𝒜 j)),
      φ (kw_lrSixU W 1 j (.inl 2)) = -(kw_lrChart_gen W j 2) ^ 2 := by sorry
