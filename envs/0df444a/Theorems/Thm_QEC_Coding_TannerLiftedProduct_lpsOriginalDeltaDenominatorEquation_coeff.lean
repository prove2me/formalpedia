-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDenominatorEquation_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDenominatorEquation_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:38:49.853725+00:00
-- url     : https://prove2.me/theorems/100fb99e-53ca-46a5-b475-d4c5d1265d7e
-- title:
--   Tanner Lifted Product: lps Original Delta Denominator Equation coeff
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Delta Denominator Equation coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L73-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L73-L90

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDenominatorEquation_coeff
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicDeltaPowerAtLevel N k)).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        Polynomial.C ((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N)) := by sorry
