-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_negativeInteriorOrders_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalField_negativeInteriorOrders_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:06:58.313232+00:00
-- url     : https://prove2.me/theorems/c4c194bc-431f-489e-9e84-11c4f80fb03e
-- title:
--   Tanner Lifted Product: lps Original Field negative Interior Orders finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Field negative Interior Orders finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L157-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L157-L180

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteNegativeDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalField_negativeInteriorOrders_finite (f : K) :
    {x : Q | lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f < 0}.Finite := by sorry
