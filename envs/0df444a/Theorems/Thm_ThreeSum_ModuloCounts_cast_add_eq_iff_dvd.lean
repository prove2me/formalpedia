-- Prove2me | Theorems.Thm_ThreeSum_ModuloCounts_cast_add_eq_iff_dvd
-- name    : ThreeSum.ModuloCounts.cast_add_eq_iff_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:33.125356+00:00
-- url     : https://prove2.me/theorems/8a0b3d15-23e2-4f73-aaa2-341e6bae653a
-- title:
--   Modulo Counts: cast add eq iff dvd
-- statement:
--   The Modulo Counts construction uses the cast add eq iff dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean#L26-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean#L26-L30

import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_ModuloCounts
set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCounts
open Finset LightResidueHistogram
open scoped BigOperators

theorem ThreeSum.ModuloCounts.cast_add_eq_iff_dvd (p : ℕ) (a b c : ℤ) :
    (a : ZMod p) + (b : ZMod p) = (c : ZMod p) ↔ (p : ℤ) ∣ c-b-a := by sorry
