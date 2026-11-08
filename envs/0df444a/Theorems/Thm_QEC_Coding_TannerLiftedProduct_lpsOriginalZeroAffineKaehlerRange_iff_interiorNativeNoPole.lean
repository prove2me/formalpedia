-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroAffineKaehlerRange_iff_interiorNativeNoPole
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehlerRange_iff_interiorNativeNoPole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:02:11.742238+00:00
-- url     : https://prove2.me/theorems/f0d1c3c4-08f7-479e-bc34-b261e4ab7deb
-- title:
--   Tanner Lifted Product: lps Original Zero Affine Kaehler Range iff interior Native No Pole
-- statement:
--   The actual zero affine Kahler image consists exactly of native differentials without interior poles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroAffineDifferentials.lean#L95-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroAffineDifferentials.lean#L95-L112

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehlerRange_iff_interiorNativeNoPole
    (omega : KaehlerDifferential ℂ K) :
    omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range ↔
      ∀ x : Q, 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN (Sum.inl x))
        (lpsOriginalNativeCovectorToLocal N hN (Sum.inl x)
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by sorry
