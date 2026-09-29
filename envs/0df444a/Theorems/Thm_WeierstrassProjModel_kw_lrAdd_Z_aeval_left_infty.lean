-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrAdd_Z_aeval_left_infty
-- name    : WeierstrassProjModel.kw_lrAdd_Z_aeval_left_infty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/fbadcad9-80a5-5245-b177-af483a5c6484
-- title:
--   Value of the addition polynomial Z at the left infinity point
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$, and consider the polynomial ring $R[X_s : s \in \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3]$ in six variables, split into a left triple $X_{\mathrm{inl}\,0},X_{\mathrm{inl}\,1},X_{\mathrm{inl}\,2}$ and a right triple $X_{\mathrm{inr}\,0},X_{\mathrm{inr}\,1},X_{\mathrm{inr}\,2}$. The $Z$-component `kw_lrAdd_Z W` of the addition law is by definition `kw_lrAdd_starZ W`, namely $c_{12}\,X_{\mathrm{inl}\,2} - c_{21}\,X_{\mathrm{inr}\,2}$, where $c_{12}$ and $c_{21}$ are the six-variable polynomials `kw_lrAdd_c₁₂ W` and `kw_lrAdd_c₂₁ W` attached to $W$. Let $A$ be a commutative $R$-algebra and $Q : \mathrm{Fin}\,3 \to A$ an arbitrary triple of elements of $A$. The assertion is that the $R$-algebra evaluation map sending the left variables to $(0,1,0)$ and the right variable $X_{\mathrm{inr}\,i}$ to $Q\,i$ carries `kw_lrAdd_Z W` to $-(Q\,2)^2$. Thus, after specialising the left argument to the point at infinity $[0:1:0]$, this addition polynomial becomes $-Z^2$ in the coordinates of the right argument, independently of $W$.
--
--   This is one of the specialisation identities for the explicit projective addition laws on a Weierstrass cubic: it records the value of the $Z$-component of the addition polynomials when the first argument is the point at infinity, the left-hand counterpart of the corresponding identity for the right argument. It is the polynomial identity underlying [`WeierstrassProjModel.kw_lrSixU_addZ_ychartL_partialEval`](thm.html#WeierstrassProjModel.kw_lrSixU_addZ_ychartL_partialEval), where the partial evaluation sending the left tensor factor to $[0:1:0]$ is computed on the generator indexed by $\mathrm{inl}\,2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrAdd_Z_aeval_left_infty.lean

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

theorem WeierstrassProjModel.kw_lrAdd_Z_aeval_left_infty
    {A : Type u} [CommRing A] [Algebra R A] (Q : Fin 3 → A) :
    MvPolynomial.aeval (R := R) (Sum.elim ![(0:A), 1, 0] Q) (kw_lrAdd_Z W)
      = -(Q 2) ^ 2 := by sorry
