-- Prove2me | Theorems.Thm_WeierstrassProjModel_isDomain_chart_of_isElliptic
-- name    : WeierstrassProjModel.isDomain_chart_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/3a91100b-98fc-57af-bb3e-480938badc67
-- title:
--   Affine charts of an elliptic projective Weierstrass model are domains
-- statement:
--   Let $R$ be a commutative ring (in a fixed universe) and let $W$ be a Weierstrass curve over $R$. Assume $R$ is an integral domain, $R$ is a Noetherian ring, and $W$ satisfies Mathlib's `IsElliptic` condition; let $i \in \{0,1,2\}$ be a chart index. Form the quotient $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,3)\,R / (F)$, where $F$ is the homogeneous cubic `polynomial` attached to the projective Weierstrass curve $W.\mathrm{toProjective}$, graded by `projModelGradingCR`, whose degree-$n$ piece is the image of the homogeneous submodule of degree-$n$ forms under the quotient map. The assertion is that the homogeneous localisation `HomogeneousLocalization.Away` of this graded ring away from the image of the variable $X_i$ — that is, the coordinate ring of the standard affine chart $D_+(x_i)$ of the projective Weierstrass model — is an integral domain: it is nontrivial and has no zero divisors.
--
--   This is the ring-theoretic form of the statement that the projective Weierstrass model of an elliptic curve over a Noetherian domain is an integral scheme, read off on each of the three standard affine charts (cf. the equivalence between integrality of a scheme and the coordinate rings of its affine opens being domains). It is invoked wherever a nonvanishing-of-a-product argument is made inside a chart ring, for instance in [`WeierstrassProjModel.kw_ev_genericPoint_zChart_psi_injective`](thm.html#WeierstrassProjModel.kw_ev_genericPoint_zChart_psi_injective) and in the two statements [`WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartL`](thm.html#WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartL) and [`WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartR`](thm.html#WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartR).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_isDomain_chart_of_isElliptic.lean

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

theorem WeierstrassProjModel.isDomain_chart_of_isElliptic
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i : Fin 3) :
    IsDomain (𝒜 i) := by sorry
