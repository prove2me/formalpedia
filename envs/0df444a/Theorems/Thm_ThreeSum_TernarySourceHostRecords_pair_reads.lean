-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostRecords_pair_reads
-- name    : ThreeSum.TernarySourceHostRecords.pair_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:57.83842+00:00
-- url     : https://prove2.me/theorems/8b31f1d9-b70d-4247-8c4e-181e62b5fca3
-- title:
--   Ternary Source Host Records: pair reads
-- statement:
--   The Ternary Source Host Records construction uses the pair reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostRecords.lean#L25-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostRecords.lean#L25-L34

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_TernarySourceHostRecords
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySourceHostRecords
open Light

theorem ThreeSum.TernarySourceHostRecords.pair_reads (ps : List (ℕ × ℕ)) (μ : ℕ → ℤ) (base : ℕ)
    (hseg : Seg μ base (WantedPairs.cells ps)) (i : ℕ) (hi : i<ps.length) :
    μ (base+2*i)=((ps.getD i (0,0)).1 : ℤ) ∧
      μ (base+2*i+1)=((ps.getD i (0,0)).2 : ℤ) := by sorry
