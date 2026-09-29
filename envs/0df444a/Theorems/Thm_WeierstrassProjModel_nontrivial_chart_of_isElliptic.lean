-- Prove2me | Theorems.Thm_WeierstrassProjModel_nontrivial_chart_of_isElliptic
-- name    : WeierstrassProjModel.nontrivial_chart_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/e28684a6-f6c0-50e0-8279-318d49f53bb1
-- title:
--   Nontriviality of the charts of a projective Weierstrass model
-- statement:
--   Let $R$ be a commutative ring that is an integral domain and Noetherian, let $W$ be a Weierstrass curve over $R$ whose discriminant is invertible (`W.IsElliptic`), and let $i \in \{0,1,2\}$ be one of the three coordinate indices. Consider the projective Weierstrass curve `W.toProjective` and its homogeneous cubic $F = Y^2Z + a_1XYZ + a_3YZ^2 - X^3 - a_2X^2Z - a_4XZ^2 - a_6Z^3$ in $R[X_0,X_1,X_2]$; the model ring is the quotient $R[X_0,X_1,X_2]/(F)$, graded by the submodules $\mathcal{G}_n$ obtained as images of the homogeneous components of degree $n$ under the quotient map, and $\mathcal{A}_i$ denotes the homogeneous localisation `HomogeneousLocalization.Away` of this graded ring at the image of $X_i$, i.e. the degree-zero part of the localisation at the powers of $\overline{X_i}$, whose elements are fractions $a/\overline{X_i}^{\,n}$ with $a$ of degree $n$. The assertion is that $\mathcal{A}_i$ is a nontrivial ring, that is $0 \neq 1$ in $\mathcal{A}_i$.
--
--   This records that each of the three standard basic opens $D_+(\overline{X_i})$ of the projective Weierstrass model is nonempty, so that the corresponding chart ring carries genuine information. It is the per-chart input used downstream, for instance in establishing that each chart ring is a domain and in the computations with generic points and with tensor products of charts in the development of the group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_nontrivial_chart_of_isElliptic.lean

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

theorem WeierstrassProjModel.nontrivial_chart_of_isElliptic
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i : Fin 3) :
    Nontrivial (𝒜 i) := by sorry
