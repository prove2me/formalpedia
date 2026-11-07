-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_degree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:36:32.835186+00:00
-- url     : https://prove2.me/theorems/59f256d5-6fd6-4f41-ac58-33ab710e68fe
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Equation degree
-- statement:
--   The constructed equation has degree at most the actual original coset cardinal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L173-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L173-L189

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_degree
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A B).natDegree ≤
      Nat.card (LPSOriginalMeromorphicCosets N) := by sorry
