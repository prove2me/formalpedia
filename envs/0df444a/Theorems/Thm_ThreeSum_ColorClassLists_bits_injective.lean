-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_bits_injective
-- name    : ThreeSum.ColorClassLists.bits_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:31.437674+00:00
-- url     : https://prove2.me/theorems/782f8a86-5f4e-4916-99ac-ddb4e9ba7c3b
-- title:
--   Color Class Lists: bits injective
-- statement:
--   The Color Class Lists construction uses the bits injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L86-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L86-L96

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter

theorem ThreeSum.ColorClassLists.bits_injective {n W : ℕ} (hn : n ≤ 2^W) :
    Function.Injective (fun i : Fin n => fun j : Fin W => i.val.testBit j.val) := by sorry
