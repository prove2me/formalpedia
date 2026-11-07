-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:38:35.826022+00:00
-- url     : https://prove2.me/theorems/dbbcbfca-9fd5-407d-a7a7-c8cc213b95a8
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Equation map
-- statement:
--   Specialization of the constructed equation is the actual Lagrange interpolant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L123-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L123-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_map
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (x : ℂ) :
    (lpsOriginalMeromorphicRatioEquation N k A B).map (Polynomial.evalRingHom x) =
      Lagrange.interpolate
        (Finset.univ : Finset (Fin (Nat.card (LPSOriginalMeromorphicCosets N)+1)))
        (fun i => (i.val : ℂ))
        (fun i => (lpsOriginalMeromorphicRatioNormCoefficient N k A B (i.val : ℂ)).eval x) := by sorry
