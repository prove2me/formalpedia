-- Prove2me | Theorems.Thm_ThreeSum_Parameters_phi_above_tangent
-- name    : ThreeSum.Parameters.phi_above_tangent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:10.978025+00:00
-- url     : https://prove2.me/theorems/6c87d69f-93c2-4089-a1e4-ca7bc3c88f8f
-- title:
--   Parameters: phi above tangent
-- statement:
--   The Parameters construction uses the phi above tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L308-L319
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L308-L319

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem ThreeSum.Parameters.phi_above_tangent {t : ℝ} (ht : 0 ≤ t) :
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by sorry
