-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_j_power_clear_interior
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalField_j_power_clear_interior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:09:41.71693+00:00
-- url     : https://prove2.me/theorems/673c6995-96a8-4d84-bc38-ff299433ce68
-- title:
--   Tanner Lifted Product: lps Original Field j power clear interior
-- statement:
--   Construct a common actual j power that clears every negative interior order supported at j zeros.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPowerPoleClearing.lean#L34-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPowerPoleClearing.lean#L34-L70

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalField_j_power_clear_interior (f : K)
    (hno : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ k : ℕ, ∀ x : Q, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      ((algebraMap P K Polynomial.X)^k*f) := by sorry
