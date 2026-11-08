-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_interior_order_nonnegative
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFieldJ_interior_order_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:09.668788+00:00
-- url     : https://prove2.me/theorems/452e22c5-6e16-42eb-92db-92ae891f8746
-- title:
--   Tanner Lifted Product: lps Original Field J interior order nonnegative
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Field J interior order nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFieldIntegral.lean#L38-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFieldIntegral.lean#L38-L54

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFieldJ_interior_order_nonnegative
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X) := by sorry
