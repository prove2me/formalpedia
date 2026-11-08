-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_sub_constant_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFieldJ_sub_constant_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:07:37.062323+00:00
-- url     : https://prove2.me/theorems/6551d066-7159-44e4-b8aa-a0428d98b49b
-- title:
--   Tanner Lifted Product: lps Original Field J sub constant ne zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Field J sub constant ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L37-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L37-L43

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
omit [NeZero N]

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFieldJ_sub_constant_ne_zero (a : ℂ) :
    algebraMap P K Polynomial.X - algebraMap ℂ K a ≠ 0 := by sorry
