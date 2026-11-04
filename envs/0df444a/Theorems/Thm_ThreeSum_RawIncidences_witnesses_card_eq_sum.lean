-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_witnesses_card_eq_sum
-- name    : ThreeSum.RawIncidences.witnesses_card_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:11.586966+00:00
-- url     : https://prove2.me/theorems/9339aedf-01cd-4b7f-8fda-c76321e668bd
-- title:
--   Raw Incidences: witnesses card eq sum
-- statement:
--   The Raw Incidences construction uses the witnesses card eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L219-L227
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L219-L227

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

theorem ThreeSum.RawIncidences.witnesses_card_eq_sum (h J : ℕ) (P d a b c : ℤ) :
    (witnesses h J P d a b c).card =
      ∑ t : ChoiceTuple h J, ∑ j : Fin 3,
        if globalModulus h J ∣ b % P - tupleLeft t ∧
          globalModulus h J ∣ c % P + d - tupleRight t ∧
          globalModulus h J ∣ (a % P + lift j * P + d) - tupleKey t
        then 1 else 0 := by sorry
