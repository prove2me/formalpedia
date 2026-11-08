-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFibre_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJFibre_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:11:05.45852+00:00
-- url     : https://prove2.me/theorems/13814c17-2f9b-4355-a396-54d8a412dce8
-- title:
--   Tanner Lifted Product: lps Original JFibre finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original JFibre finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L132-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L132-L141

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
include hpos hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJFibre_finite (a : ℂ) :
    {y : Q | lpsOriginalFilledJ N (Sum.inl y) = a}.Finite := by sorry
