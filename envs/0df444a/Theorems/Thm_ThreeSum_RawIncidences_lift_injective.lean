-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_lift_injective
-- name    : ThreeSum.RawIncidences.lift_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:32.264786+00:00
-- url     : https://prove2.me/theorems/c0702b2a-4b09-47d9-a478-d474beab1026
-- title:
--   Raw Incidences: lift injective
-- statement:
--   The Raw Incidences construction uses the lift injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L30-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L30-L34

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

theorem ThreeSum.RawIncidences.lift_injective : Function.Injective lift := by sorry
