-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_lift_small
-- name    : ThreeSum.RawIncidences.lift_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:17.510198+00:00
-- url     : https://prove2.me/theorems/01e9ea5e-c741-4e2a-ab79-078a61fbe7c0
-- title:
--   Raw Incidences: lift small
-- statement:
--   The Raw Incidences construction uses the lift small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L27-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L27-L28

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds

theorem ThreeSum.RawIncidences.lift_small (j : Fin 3) : Arithmetic.SmallLift (lift j) := by sorry
