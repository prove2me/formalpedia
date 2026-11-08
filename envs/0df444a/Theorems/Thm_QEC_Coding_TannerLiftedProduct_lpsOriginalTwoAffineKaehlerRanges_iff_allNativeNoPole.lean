-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:10:18.334851+00:00
-- url     : https://prove2.me/theorems/f9fe2c77-8fd7-42ac-bea5-53453a453a9f
-- title:
--   Tanner Lifted Product: lps Original Two Affine Kaehler Ranges iff all Native No Pole
-- statement:
--   Membership in both actual affine Kahler images is exactly native no poles at every filled-curve point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalTwoChartDifferentials.lean#L64-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalTwoChartDifferentials.lean#L64-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalTwoChartDifferentials
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary016
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary024
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary025
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary026

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole
    (omega : KaehlerDifferential ℂ K) :
    (omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range ∧
      omega ∈ (KaehlerDifferential.map ℂ ℂ I K).range) ↔
      ∀ x : LPSOriginalFilledCurve N,
        0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
          (lpsOriginalNativeCovectorToLocal N hN x
            (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by sorry
