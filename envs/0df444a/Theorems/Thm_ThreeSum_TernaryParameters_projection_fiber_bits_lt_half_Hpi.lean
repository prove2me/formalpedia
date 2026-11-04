-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_projection_fiber_bits_lt_half_Hpi
-- name    : ThreeSum.TernaryParameters.projection_fiber_bits_lt_half_Hpi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:55:28.761928+00:00
-- url     : https://prove2.me/theorems/206a051c-5d03-4709-9bfd-7896708dd6fc
-- title:
--   Ternary Parameters: projection fiber bits lt half Hpi
-- statement:
--   The Ternary Parameters construction uses the projection fiber bits lt half Hpi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L450-L453
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L450-L453

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem ThreeSum.TernaryParameters.projection_fiber_bits_lt_half_Hpi {m : ℕ} (hm : 0 < m) :
    Real.log (((100000000 * m).choose (978268 * m) : ℕ) : ℝ) /
      ((100000000 * m : ℕ) * Real.log 2) < Hpi / 2 := by sorry
