-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicMonicEquation_monic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicMonicEquation_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:39:19.108395+00:00
-- url     : https://prove2.me/theorems/1a9677c0-f6fb-48b4-988f-ceee13994c52
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Monic Equation monic
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Holomorphic Monic Equation monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L98-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L98-L110

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicMonicEquation_monic (N : ℕ) [NeZero N] (k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalHolomorphicMonicEquation N k A).Monic := by sorry
