-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityAffineKaehler_nativeNoPole
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityAffineKaehler_nativeNoPole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:00:48.824339+00:00
-- url     : https://prove2.me/theorems/d7263440-6df3-4e63-8ca9-0ef0c62077a8
-- title:
--   Tanner Lifted Product: lps Original Infinity Affine Kaehler native No Pole
-- statement:
--   Actual reciprocal-chart affine differential preimages have no native pole at each point of that chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityAffineDifferentials.lean#L66-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityAffineDifferentials.lean#L66-L76

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPointCoverage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary016
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary024

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityAffineKaehler_nativeNoPole
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (omega : KaehlerDifferential ℂ K)
    (h : omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range) :
    0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by sorry
