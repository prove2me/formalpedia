-- Prove2me | Theorems.Thm_ThreeSum_ModuloCounts_count_eq_tripleMass
-- name    : ThreeSum.ModuloCounts.count_eq_tripleMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:22.883871+00:00
-- url     : https://prove2.me/theorems/a26ff344-7e60-4c8f-ba4a-3b6dd6548874
-- title:
--   Modulo Counts: count eq triple Mass
-- statement:
--   The Modulo Counts construction uses the count eq triple Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean#L32-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean#L32-L40

import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_ModuloCounts
set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCounts
open Finset LightResidueHistogram
open scoped BigOperators

theorem ThreeSum.ModuloCounts.count_eq_tripleMass {p : ℕ} [NeZero p]
    (nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c =
      Histograms.tripleMass (range nA) (range nB) (range nC)
        (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p))
        (fun i => (c i : ZMod p)) (fun _ => 1) (fun _ => 1) (fun _ => 1) := by sorry
