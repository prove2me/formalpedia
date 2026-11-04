-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_tupleRight_of_signature
-- name    : ThreeSum.RawIncidences.tupleRight_of_signature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:08.573508+00:00
-- url     : https://prove2.me/theorems/4551aa17-6aa8-4bcf-8551-a9193a727dc5
-- title:
--   Raw Incidences: tuple Right of signature
-- statement:
--   The Raw Incidences construction uses the tuple Right of signature property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L95-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L95-L109

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

theorem ThreeSum.RawIncidences.tupleRight_of_signature {h J : ℕ} {s t : ChoiceTuple h J}
    (he : rightSignature s = rightSignature t) : tupleRight s = tupleRight t := by sorry
