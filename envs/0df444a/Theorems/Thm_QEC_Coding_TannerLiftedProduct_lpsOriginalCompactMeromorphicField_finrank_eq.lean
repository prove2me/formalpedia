-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicField_finrank_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicField_finrank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:09:53.785414+00:00
-- url     : https://prove2.me/theorems/cab6338e-17aa-4906-9279-a913c95f555a
-- title:
--   Tanner Lifted Product: lps Original Compact Meromorphic Field finrank eq
-- statement:
--   The ENTIRE actual compact meromorphic field has the genuine original Gamma0 coset degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicFunctionField.lean#L385-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicFunctionField.lean#L385-L394

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicField_finrank_eq
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ))
      (LPSOriginalCompactMeromorphicGermRing N hN) =
        Nat.card (LPSOriginalMeromorphicCosets N) := by sorry
