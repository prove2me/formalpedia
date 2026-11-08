-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphic_generated_representation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphic_generated_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:11:52.598198+00:00
-- url     : https://prove2.me/theorems/e6617aa4-0da5-41ab-81fd-5487f02d73d5
-- title:
--   Tanner Lifted Product: lps Original Compact Meromorphic generated representation
-- statement:
--   Every actual original compact meromorphic function has a SAME C(j,j_N) representation in genuine global germs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicFunctionField.lean#L397-L412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicFunctionField.lean#L397-L412

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphic_generated_representation
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∃ x : lpsOriginalGeneratedFunctionField N hpos,
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN x).val =
        (F : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) := by sorry
