-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicField_finiteDimensional
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicField_finiteDimensional
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:09:09.361425+00:00
-- url     : https://prove2.me/theorems/54403154-b45d-41c7-9ab1-d00167129414
-- title:
--   Tanner Lifted Product: lps Original Compact Meromorphic Field finite Dimensional
-- statement:
--   The ENTIRE actual compact meromorphic field is finite dimensional over SAME C(j).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicFunctionField.lean#L373-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicFunctionField.lean#L373-L382

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicField_finiteDimensional
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    FiniteDimensional (FractionRing (Polynomial ℂ))
      (LPSOriginalCompactMeromorphicGermRing N hN) := by sorry
