-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrAdd_Z_aeval_right_infty
-- name    : WeierstrassProjModel.kw_lrAdd_Z_aeval_right_infty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/b0ec4383-7617-5433-b4c3-01b93ed1d805
-- title:
--   The Z addition polynomial at the right point at infinity
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$, and let $A$ be a commutative $R$-algebra (in the same universe) together with a triple $P \colon \mathrm{Fin}\,3 \to A$, thought of as a candidate set of projective coordinates. The addition polynomial `kw_lrAdd_Z W` lives in the polynomial ring $R[X_s : s \in \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3]$ in two groups of three homogeneous coordinates, and is by definition `kw_lrAdd_starZ W`, namely $c_{12}\,X_{\mathrm{inl}\,2} - c_{21}\,X_{\mathrm{inr}\,2}$, where $c_{12}$ and $c_{21}$ are the bihomogeneous polynomials `kw_lrAdd_c₁₂ W` and `kw_lrAdd_c₂₁ W` in the same six variables. The assertion is that the $R$-algebra evaluation map sending the left-hand variables $X_{\mathrm{inl}\,i}$ to $P_i$ and the right-hand variables $X_{\mathrm{inr}\,0}, X_{\mathrm{inr}\,1}, X_{\mathrm{inr}\,2}$ to $0, 1, 0$ respectively carries `kw_lrAdd_Z W` to $P_2^{\,2}$; that is, specialising the second argument to the point at infinity $[0:1:0]$ turns the $Z$-coordinate of this addition law into the square of the $Z$-coordinate of the first argument.
--
--   This is the polynomial identity expressing that the $Z$-component of the chord addition law degenerates, at the right-hand point at infinity, to the square of the left-hand $Z$-coordinate, so that the addition law specialises to the identity on the projective Weierstrass model up to the scalar $P_2^2$. It is used in the analysis of the addition law on the standard affine chart, where it supplies the value of the $Z$-coordinate under partial evaluation at the point at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrAdd_Z_aeval_right_infty.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas

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

theorem WeierstrassProjModel.kw_lrAdd_Z_aeval_right_infty
    {A : Type u} [CommRing A] [Algebra R A] (P : Fin 3 → A) :
    MvPolynomial.aeval (R := R) (Sum.elim P ![(0:A), 1, 0]) (kw_lrAdd_Z W)
      = P 2 ^ 2 := by sorry
