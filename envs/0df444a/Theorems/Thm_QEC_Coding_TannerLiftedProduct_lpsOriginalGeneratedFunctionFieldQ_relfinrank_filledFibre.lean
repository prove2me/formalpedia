-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_relfinrank_filledFibre
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_relfinrank_filledFibre
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:34:40.949182+00:00
-- url     : https://prove2.me/theorems/d8428536-8649-4fc8-809d-f85e1b18c8dc
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field Q relfinrank filled Fibre
-- statement:
--   The same original relative degree equals every full filled fibre cardinality over an interior point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L769-L782
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L769-L782

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_relfinrank_filledFibre
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ M hposM) =
      Nat.card {x : LPSOriginalFilledCurve M |
        lpsOriginalFilledForgetLevel N M hNM x = Sum.inl y} := by sorry
