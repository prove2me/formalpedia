-- Prove2me | Theorems.Thm_ThreeSum_ModuloCounts_count_eq_correlation
-- name    : ThreeSum.ModuloCounts.count_eq_correlation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:24.768051+00:00
-- url     : https://prove2.me/theorems/23cdcbd3-8a5f-4bc8-bce0-e395034c8a8b
-- title:
--   Modulo Counts: count eq correlation
-- statement:
--   The Modulo Counts construction uses the count eq correlation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean#L42-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean#L42-L49

import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_ModuloCounts
set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCounts
open Finset LightResidueHistogram
open scoped BigOperators

theorem ThreeSum.ModuloCounts.count_eq_correlation {p : ℕ} [NeZero p]
    (nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c =
      ∑ i ∈ range nA, Balancing.correlation
        (signedHistogram p 1 c nC) (signedHistogram p 1 b nB) (a i : ZMod p) := by sorry
