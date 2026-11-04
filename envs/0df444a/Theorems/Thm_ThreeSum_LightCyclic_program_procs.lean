-- Prove2me | Theorems.Thm_ThreeSum_LightCyclic_program_procs
-- name    : ThreeSum.LightCyclic.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:03.569832+00:00
-- url     : https://prove2.me/theorems/523b7db7-648b-4a05-9bc2-43e6bc095cbd
-- title:
--   Light Cyclic: program procs
-- statement:
--   The Light Cyclic construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L140-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L140-L140

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCyclic.program_procs : LightKaratsuba.Procs program 1 2 3 4 := by sorry
