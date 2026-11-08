-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicValuationRing_essFiniteType
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicValuationRing_essFiniteType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:14:23.70462+00:00
-- url     : https://prove2.me/theorems/4fc8cf57-2ece-460e-814f-f697b7be93c4
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Valuation Ring ess Finite Type
-- statement:
--   Every actual filled-point valuation ring is essentially finite type, using the real interior and cusp chart cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerInjective.lean#L76-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerInjective.lean#L76-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerFiniteness
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary008
variable (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary016
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary023

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicValuationRing_essFiniteType :
    Algebra.EssFiniteType ℂ V := by sorry
