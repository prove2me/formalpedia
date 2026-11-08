-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_reciprocal_integral_iff_regularPoints
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_integral_iff_regularPoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:06:16.986561+00:00
-- url     : https://prove2.me/theorems/c04aa3a0-5026-448d-a651-114a1252bdc8
-- title:
--   Tanner Lifted Product: lps Original Field reciprocal integral iff regular Points
-- statement:
--   Same-field reciprocal integrality is exactly nonnegative order at every point of the actual reciprocal domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityFiniteFibres.lean#L68-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityFiniteFibres.lean#L68-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityFiniteFibresDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityFiniteFibresDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityFiniteFibresDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityFiniteFibresDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_integral_iff_regularPoints (f : K) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f ↔
      ∀ x : S, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val f := by sorry
