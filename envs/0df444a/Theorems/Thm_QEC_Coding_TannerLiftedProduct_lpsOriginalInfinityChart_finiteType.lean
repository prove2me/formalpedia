-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityChart_finiteType
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChart_finiteType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:11:58.658029+00:00
-- url     : https://prove2.me/theorems/58be18b7-5439-4e44-b089-e696738a5365
-- title:
--   Tanner Lifted Product: lps Original Infinity Chart finite Type
-- statement:
--   The actual reciprocal normalization is finite type over literal complex constants, with the true reciprocal polynomial fraction embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerFiniteness.lean#L129-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerFiniteness.lean#L129-L149

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
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary027
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary029
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary030
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary040
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary043

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChart_finiteType : Algebra.FiniteType ℂ R := by sorry
