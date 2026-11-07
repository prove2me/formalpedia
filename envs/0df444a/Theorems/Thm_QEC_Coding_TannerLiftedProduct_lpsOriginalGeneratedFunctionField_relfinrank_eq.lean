-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_relfinrank_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_relfinrank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:09:59.517201+00:00
-- url     : https://prove2.me/theorems/a3b013f2-6d36-4bd7-95e0-c8690503daf6
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field relfinrank eq
-- statement:
--   The relative degree of the same original generated fields equals the actual integral congruence-subgroup relative index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeFunctionFieldDegree.lean#L22-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeFunctionFieldDegree.lean#L22-L60

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_relfinrank_eq
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField M hposM) =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by sorry
