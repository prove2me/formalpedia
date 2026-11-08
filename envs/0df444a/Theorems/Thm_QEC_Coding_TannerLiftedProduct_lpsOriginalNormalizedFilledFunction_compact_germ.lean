-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_compact_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_compact_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:30:22.942236+00:00
-- url     : https://prove2.me/theorems/6cb3418a-8b75-42f5-ac46-22e29c9fa7d1
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Function compact germ
-- statement:
--   Normalization retains the genuine compact meromorphic field class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean#L115-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean#L115-L129

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary004

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_compact_germ
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalCompactMeromorphicGermAlgHom N hN
      ⟨lpsOriginalNormalizedFilledFunction N hN F,
        lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF⟩ =
      lpsOriginalCompactMeromorphicGermAlgHom N hN ⟨F,hF⟩ := by sorry
