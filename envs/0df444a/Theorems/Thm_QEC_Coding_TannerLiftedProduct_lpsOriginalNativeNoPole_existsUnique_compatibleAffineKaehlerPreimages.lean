-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeNoPole_existsUnique_compatibleAffineKaehlerPreimages
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNativeNoPole_existsUnique_compatibleAffineKaehlerPreimages
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:30:52.52472+00:00
-- url     : https://prove2.me/theorems/dfaa03b0-fde5-419a-a8cd-1778f696d50d
-- title:
--   Tanner Lifted Product: lps Original Native No Pole exists Unique compatible Affine Kaehler Preimages
-- statement:
--   Construct the unique pair of actual affine preimages with equal Laurent restrictions from native no poles at every filled point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAffineKaehlerCompatibility.lean#L135-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAffineKaehlerCompatibility.lean#L135-L150

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerInjective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalTwoChartDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary016
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary024
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary025
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary026
local notation "L" => LaurentPolynomial ℂ
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary027
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary029
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary030
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary040
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary043
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary044
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary046
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary051
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary052
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary053
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerCompatibilityDictionary054

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNativeNoPole_existsUnique_compatibleAffineKaehlerPreimages
    (omega : KaehlerDifferential ℂ K)
    (h : ∀ x : LPSOriginalFilledCurve N, 0 ≤ meromorphicOrderValuation
      (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃! pair : KaehlerDifferential ℂ R × KaehlerDifferential ℂ I,
      KaehlerDifferential.map ℂ ℂ R K pair.1 = omega ∧
      KaehlerDifferential.map ℂ ℂ I K pair.2 = omega ∧
      KaehlerDifferential.map ℂ ℂ R T pair.1 = KaehlerDifferential.map ℂ ℂ I T pair.2 := by sorry
