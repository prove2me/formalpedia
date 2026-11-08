-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_reciprocal_integral_of_noPole
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_integral_of_noPole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:30:40.386314+00:00
-- url     : https://prove2.me/theorems/288227b3-a92e-4cc6-9a8f-14b623b580fb
-- title:
--   Tanner Lifted Product: lps Original Field reciprocal integral of no Pole
-- statement:
--   Actual reciprocal-regular local orders construct an E4 numerator and prove SAME C[1/j] integrality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean#L151-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean#L151-L205

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_integral_of_noPole
    (f : K)
    (hi : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f)
    (hc : ∀ c : C, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c) f) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f := by sorry
