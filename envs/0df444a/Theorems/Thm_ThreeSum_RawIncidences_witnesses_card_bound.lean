-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_witnesses_card_bound
-- name    : ThreeSum.RawIncidences.witnesses_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:09.646551+00:00
-- url     : https://prove2.me/theorems/ebdbc6e3-9dd4-4816-9fec-29a094d6d60c
-- title:
--   Raw Incidences: witnesses card bound
-- statement:
--   The Raw Incidences construction uses the witnesses card bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L208-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L208-L217

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

theorem ThreeSum.RawIncidences.witnesses_card_bound {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    (witnesses h J P d a b c).card ≤ representationCap h J := by sorry
