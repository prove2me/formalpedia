-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroAffineKaehler_localClear
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehler_localClear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:01:18.72287+00:00
-- url     : https://prove2.me/theorems/649eb1c7-5515-4c46-9143-ed1c2bfd8e23
-- title:
--   Tanner Lifted Product: lps Original Zero Affine Kaehler local Clear
-- statement:
--   A native differential without a local pole has a clearing scalar outside the actual zero evaluation kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroAffineDifferentials.lean#L80-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroAffineDifferentials.lean#L80-L91

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroPointCoverage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary016
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary024

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehler_localClear
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (omega : KaehlerDifferential ℂ K)
    (h : 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃ s : R, s ∉ RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj) ∧
      s • omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range := by sorry
