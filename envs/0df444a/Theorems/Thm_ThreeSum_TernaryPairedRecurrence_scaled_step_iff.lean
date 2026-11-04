-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedRecurrence_scaled_step_iff
-- name    : ThreeSum.TernaryPairedRecurrence.scaled_step_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:48.554168+00:00
-- url     : https://prove2.me/theorems/ed00dbec-0fd1-40e3-a533-3828132ab0b2
-- title:
--   Ternary Paired Recurrence: scaled step iff
-- statement:
--   The physical query tensor may carry a positive common factorial
--   scale at each prefix. Integer cross multiplication removes both scales.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L79-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L79-L89

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence

theorem ThreeSum.TernaryPairedRecurrence.scaled_step_iff (a b old next sOld sNext : ℕ)
    (hOld : 0<sOld) (hNext : 0<sNext) :
    a*sOld*(sNext*next)≤b*sNext*(sOld*old) ↔ a*next≤b*old := by sorry
