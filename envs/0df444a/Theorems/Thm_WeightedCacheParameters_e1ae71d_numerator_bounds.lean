-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_numerator_bounds
-- name    : WeightedCacheParameters_e1ae71d.numerator_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:15.929416+00:00
-- url     : https://prove2.me/theorems/c4877288-b96d-44fa-ae5a-3cd5caf51680
-- title:
--   numerator_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L402-L414
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L402-L414

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

theorem WeightedCacheParameters_e1ae71d.numerator_bounds :
    2 * Bn < targetExponent * Hn ∧
    2 * Hn - Gn + 2 * Qn < targetExponent * Hn ∧
    2 * An < targetExponent * Hn ∧
    Hn + Gn < targetExponent * Hn ∧
    2 * Hn - Gn < targetExponent * Hn := by sorry
