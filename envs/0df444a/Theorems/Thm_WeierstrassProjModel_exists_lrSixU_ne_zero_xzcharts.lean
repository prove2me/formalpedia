-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_xzcharts
-- name    : WeierstrassProjModel.exists_lrSixU_ne_zero_xzcharts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/875e2331-dc80-55db-a95f-115ab63703b4
-- title:
--   Some Lange–Ruppert u_l is nonzero on a chart tensor product
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and Noetherian, and let $W$ be a Weierstrass curve over $R$ whose discriminant is a unit (`W.IsElliptic`). Write $\mathcal A_i$, for $i \in \mathrm{Fin}\,3$, for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(F)$ at the image of the variable $X_i$, where $F$ is the projective Weierstrass polynomial of $W$, the ideal is the homogeneous ideal it spans, and the grading is the image of the homogeneous submodules of the polynomial ring under the quotient map; thus $\mathcal A_i$ is the coordinate ring of the affine chart $X_i \neq 0$ of the projective Weierstrass model, viewed as an $R$-algebra via the structure map from degree zero. For indices $i, j \in \mathrm{Fin}\,3$ with $i \neq 1$ and $j \neq 1$, the assertion is that there exists an index $l \in \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$ such that the element $\mathrm{kw\_lrSixU}\,W\,i\,j\,l$ of $\mathcal A_i \otimes_R \mathcal A_j$ is nonzero, where this family of six elements is the sum-elimination of the three dehomogenised Lange–Ruppert addition-law coordinates `kw_lrChart_u` and the three coordinates `kw_lrSymChart_u` of the symmetric companion law, each evaluated on the chart pair $(i,j)$.
--
--   This is the non-degeneracy input for the Lange–Ruppert complete system of addition laws on the projective Weierstrass model: on each pair of standard charts, at least one of the six addition-law coordinate functions does not vanish identically. It is cited by [`WeierstrassProjModel.exists_lrSixU_ne_zero_of_isElliptic`](thm.html#WeierstrassProjModel.exists_lrSixU_ne_zero_of_isElliptic), which removes the restriction on the chart indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_xzcharts.lean

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

theorem WeierstrassProjModel.exists_lrSixU_ne_zero_xzcharts
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (i j : Fin 3) (hi : i ≠ 1) (hj : j ≠ 1) :
    ∃ l, kw_lrSixU W i j l ≠ 0 := by sorry
