-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalPolynomialMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalPolynomialMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:11.885216+00:00
-- url     : https://prove2.me/theorems/59f8ed74-c87f-404c-a028-706e45acffb7
-- title:
--   Tanner Lifted Product: lps Original Reciprocal Polynomial Map injective
-- statement:
--   The actual reciprocal polynomial map into the same original generated field is faithful.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityPoleClearingAway.lean#L28-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityPoleClearingAway.lean#L28-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityPoleClearingAwayDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
omit [NeZero N]

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalPolynomialMap_injective :
    Function.Injective (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos) := by sorry
