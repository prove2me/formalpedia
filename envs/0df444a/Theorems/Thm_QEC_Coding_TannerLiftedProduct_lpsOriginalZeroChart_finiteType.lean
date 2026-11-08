-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroChart_finiteType
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChart_finiteType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:08:52.921744+00:00
-- url     : https://prove2.me/theorems/c64ed4bf-c926-456d-9792-d57d440be13d
-- title:
--   Tanner Lifted Product: lps Original Zero Chart finite Type
-- statement:
--   The actual zero normalization is a finite-type complex algebra, using its finite separable function-field extension and literal constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerFiniteness.lean#L54-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerFiniteness.lean#L54-L62

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerFiniteness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary016
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary018

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChart_finiteType : Algebra.FiniteType ℂ R := by sorry
