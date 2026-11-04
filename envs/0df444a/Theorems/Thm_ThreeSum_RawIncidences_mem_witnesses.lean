-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_mem_witnesses
-- name    : ThreeSum.RawIncidences.mem_witnesses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:14.913638+00:00
-- url     : https://prove2.me/theorems/7d5a926d-ed06-4df7-8cad-b38f05714376
-- title:
--   Raw Incidences: mem witnesses
-- statement:
--   The Raw Incidences construction uses the mem witnesses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L144-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L144-L148

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

theorem ThreeSum.RawIncidences.mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : Witness h J} :
    w ∈ witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
        globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1 := by sorry
