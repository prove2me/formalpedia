-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityValuation_essFiniteType
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityValuation_essFiniteType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:12:05.797091+00:00
-- url     : https://prove2.me/theorems/d131672c-7092-4895-804e-7af2a4018ad4
-- title:
--   Tanner Lifted Product: lps Original Infinity Valuation ess Finite Type
-- statement:
--   The actual reciprocal-chart point valuation ring is essentially finite type by genuine height-one localization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerFiniteness.lean#L169-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerFiniteness.lean#L169-L175

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
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary044
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary046
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary051

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityValuation_essFiniteType
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    Algebra.EssFiniteType ℂ V := by sorry
