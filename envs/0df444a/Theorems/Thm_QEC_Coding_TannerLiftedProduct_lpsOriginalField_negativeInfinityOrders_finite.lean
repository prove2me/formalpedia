-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_negativeInfinityOrders_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalField_negativeInfinityOrders_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:06:12.749658+00:00
-- url     : https://prove2.me/theorems/5b77ae67-735c-444a-9fe1-4917001aec8a
-- title:
--   Tanner Lifted Product: lps Original Field negative Infinity Orders finite
-- statement:
--   An arbitrary element of the original generated field has finitely many negative orders on the actual reciprocal domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityFiniteFibres.lean#L53-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityFiniteFibres.lean#L53-L65

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalField_negativeInfinityOrders_finite (f : K) :
    {x : S | lpsOriginalFieldLocalOrder N hN hpos x.val f < 0}.Finite := by sorry
