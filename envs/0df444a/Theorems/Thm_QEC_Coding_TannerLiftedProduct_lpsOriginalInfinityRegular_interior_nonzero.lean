-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityRegular_interior_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityRegular_interior_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:02:17.502851+00:00
-- url     : https://prove2.me/theorems/36b07bcd-40d8-4fd7-b60f-c4078bf9e648
-- title:
--   Tanner Lifted Product: lps Original Infinity Regular interior nonzero
-- statement:
--   Actual inverse-j regularity excludes interior j zeros by positive finite j order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityRegularPoints.lean#L79-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityRegularPoints.lean#L79-L94

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityRegularPointsDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityRegularPointsDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityRegularPointsDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityRegularPointsDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityRegular_interior_nonzero
    (x : Q) (hx : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X)⁻¹) : lpsOriginalFilledJ N (Sum.inl x) ≠ 0 := by sorry
