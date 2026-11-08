-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedRestriction_representative
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedRestriction_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:08:30.000202+00:00
-- url     : https://prove2.me/theorems/156b6b0d-17df-4c1e-a4bf-525c1d5cc13a
-- title:
--   Tanner Lifted Product: lps Original Generated Restriction representative
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Generated Restriction representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFieldIntegral.lean#L56-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFieldIntegral.lean#L56-L73

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "E" => lpsOriginalFilledMeromorphicRestrictionSubfield N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary003

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedRestriction_representative
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f =
      lpsOriginalFilledMeromorphicRestriction N hN F.val F.property := by sorry
