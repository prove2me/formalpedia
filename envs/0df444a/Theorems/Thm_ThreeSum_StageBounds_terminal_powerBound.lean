-- Prove2me | Theorems.Thm_ThreeSum_StageBounds_terminal_powerBound
-- name    : ThreeSum.StageBounds.terminal_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:02.563049+00:00
-- url     : https://prove2.me/theorems/6d235dcc-4554-4db0-987c-a95fb9f6063c
-- title:
--   Stage Bounds: terminal power Bound
-- statement:
--   The Stage Bounds construction uses the terminal power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L192-L204
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StageBounds.lean#L192-L204

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.StageBounds.terminal_powerBound {H P H1 : ℕ → ℕ} (k : ℕ)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound (terminalCount H)
      (2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa)) := by sorry
