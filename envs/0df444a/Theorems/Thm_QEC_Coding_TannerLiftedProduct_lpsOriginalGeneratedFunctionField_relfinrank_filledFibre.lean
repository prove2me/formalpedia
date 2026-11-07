-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_relfinrank_filledFibre
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_relfinrank_filledFibre
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:09:47.462607+00:00
-- url     : https://prove2.me/theorems/6d2c4c9b-de25-4d60-bfa4-5917df7a0899
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field relfinrank filled Fibre
-- statement:
--   The same original relative degree equals every full filled fibre cardinality over an interior point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeFunctionFieldDegree.lean#L63-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeFunctionFieldDegree.lean#L63-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_relfinrank_filledFibre
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField M hposM) =
      Nat.card {x : LPSOriginalFilledCurve M |
        lpsOriginalFilledForgetLevel N M hNM x = Sum.inl y} := by sorry
