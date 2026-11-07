-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:17:38.429954+00:00
-- url     : https://prove2.me/theorems/888c4e47-9f5f-4d74-ab6c-fee612296d2c
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field Q relfinrank eq
-- statement:
--   The relative degree of the same original generated fields equals the actual integral congruence-subgroup relative index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L728-L766
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L728-L766

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ M hposM) =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by sorry
