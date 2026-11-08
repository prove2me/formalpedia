-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_j_power_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalField_j_power_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:36:00.015298+00:00
-- url     : https://prove2.me/theorems/4bf96304-a7ae-4ffc-a0e8-561bc001ebb1
-- title:
--   Tanner Lifted Product: lps Original Field j power integral
-- statement:
--   The constructed common j power makes the actual cleared element integral over the original zero base.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPowerPoleClearing.lean#L73-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPowerPoleClearing.lean#L73-L78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalField_j_power_integral (f : K)
    (hno : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ k : ℕ, IsIntegral P ((algebraMap P K Polynomial.X)^k*f) := by sorry
