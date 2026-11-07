-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_inverseTailDifference_eq_shiftedCorrection_add_boundary
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.inverseTailDifference_eq_shiftedCorrection_add_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:43.526392+00:00
-- url     : https://prove2.me/theorems/179aacc2-9e75-48c7-be48-96665851e0cd
-- title:
--   Cartwright Steger: inverse Tail Difference eq shifted Correction add boundary
-- statement:
--   The full inverse-tail difference telescopes to the shifted correction
--   sum plus the explicit cyclic-boundary contribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1019-L1042
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1019-L1042

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.inverseTailDifference_eq_shiftedCorrection_add_boundary
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityLeadingMonomial P r k ζ *
          constantConjugatedBInverseTail P r u -
        infinityDefectMonomial P r u k ζ *
          constantConjugatedBInverseTail P r u =
      (∑ i ∈ Finset.range r.matrixRank,
          infinityShiftedCorrectionTerm P r u k i ζ) +
        (onePlusY P r) • infinityDefectTailTerm P r u k 0 ζ -
          infinityDefectTailTerm P r u k 0 ζ := by sorry
