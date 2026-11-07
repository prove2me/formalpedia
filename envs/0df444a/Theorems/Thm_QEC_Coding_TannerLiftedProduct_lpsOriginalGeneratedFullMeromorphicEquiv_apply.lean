-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFullMeromorphicEquiv_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFullMeromorphicEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:06:10.581208+00:00
-- url     : https://prove2.me/theorems/b260ff31-4a83-4d61-8d7c-b73e40e300b7
-- title:
--   Tanner Lifted Product: lps Original Generated Full Meromorphic Equiv apply
-- statement:
--   The equivalence has the literal proved holomorphic-fraction germ values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullMeromorphicFunctionField.lean#L191-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullMeromorphicFunctionField.lean#L191-L199

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFullMeromorphicEquiv_apply
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ x : lpsOriginalGeneratedFunctionField N hpos,
      (lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN x).val =
        lpsOriginalHolomorphicFractionToMeromorphicGerm x.val := by sorry
