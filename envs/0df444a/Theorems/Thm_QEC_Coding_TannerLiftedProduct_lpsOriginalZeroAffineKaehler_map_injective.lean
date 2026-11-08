-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroAffineKaehler_map_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehler_map_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:21:02.525579+00:00
-- url     : https://prove2.me/theorems/e8ee7765-d0d2-4de2-a77e-d63bea1aa777
-- title:
--   Tanner Lifted Product: lps Original Zero Affine Kaehler map injective
-- statement:
--   Actual maximal-point coverage and local kernel clearing prove the zero-affine differential map injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAffineKaehlerInjective.lean#L82-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAffineKaehlerInjective.lean#L82-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerInjective
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary016
include hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehler_map_injective :
    Function.Injective (KaehlerDifferential.map ℂ ℂ R K) := by sorry
