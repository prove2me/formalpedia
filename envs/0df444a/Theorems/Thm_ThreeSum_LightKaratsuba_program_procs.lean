-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_program_procs
-- name    : ThreeSum.LightKaratsuba.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:57.616396+00:00
-- url     : https://prove2.me/theorems/0a4dced9-9d9f-4c6a-a82b-9450453c94d3
-- title:
--   Light Karatsuba: program procs
-- statement:
--   The Light Karatsuba construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L647-L647
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L647-L647

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}

theorem ThreeSum.LightKaratsuba.program_procs : Procs program 0 1 2 3 := by sorry
