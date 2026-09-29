-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrSixU_locMap_isSchemeTheoreticallyDominant
-- name    : WeierstrassProjModel.kw_lrSixU_locMap_isSchemeTheoreticallyDominant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/3d90e2ee-1209-52d3-b281-d62a5b52d028
-- title:
--   Dominance of the six-U localisation maps on a chart product
-- statement:
--   Let $R$ be a commutative ring which is a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ satisfying `W.IsElliptic`. For a chart index $i \in \mathrm{Fin}\,3$ write $\mathcal A_i$ for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the graded ring $R[X_0,X_1,X_2]/(F)$ — where $F$ is the projective Weierstrass cubic of $W$ and the grading is the image of the usual grading under the quotient map — at the image of the variable $X_i$; thus $\mathcal A_i$ is the coordinate ring of the $i$-th affine chart, regarded as an $R$-algebra via the degree-zero part. Fix $i, j \in \mathrm{Fin}\,3$ and an index $l \in \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$, and let $u_l \in \mathcal A_i \otimes_R \mathcal A_j$ be the corresponding member of the six-element family `kw_lrSixU W i j`, given on the left summand by the Lange–Ruppert addition-law vector evaluated in the charts $i,j$ and on the right summand by its symmetrised counterpart. Assume $u_l \neq 0$. Then the morphism `kw_lrSixU_locMap W i j l`, namely $\operatorname{Spec}$ of the localisation map $\mathcal A_i \otimes_R \mathcal A_j \to (\mathcal A_i \otimes_R \mathcal A_j)[u_l^{-1}]$, is scheme-theoretically dominant.
--
--   This is the density statement that allows two morphisms out of $\operatorname{Spec}(\mathcal A_i \otimes_R \mathcal A_j)$ agreeing on the basic open set $D(u_l)$ to be identified: the inclusion of that basic open is dominant even scheme-theoretically, the ambient affine scheme being integral. It is used in the construction of the addition morphism on the projective Weierstrass model chart by chart, in `perChart_addMorphism_pin_over`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrSixU_locMap_isSchemeTheoreticallyDominant.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

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

theorem WeierstrassProjModel.kw_lrSixU_locMap_isSchemeTheoreticallyDominant
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) (hl : kw_lrSixU W i j l ≠ 0) :
    IsSchemeTheoreticallyDominant (kw_lrSixU_locMap W i j l) := by sorry
