-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryColorPrelude_header_reads
-- name    : ThreeSum.LightTernaryColorPrelude.header_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:39:26.002598+00:00
-- url     : https://prove2.me/theorems/00db26a0-f45d-4da3-99f4-6d2382093bec
-- title:
--   Light Ternary Color Prelude: header reads
-- statement:
--   The Light Ternary Color Prelude construction uses the header reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L283-L298
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L283-L298

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryColorPrelude.header_reads {μ : ℕ→ℤ} {free n : ℕ} {A B C : List ℤ}
    (H : Seg μ free (header free n A B C)) :
    μ free=(av free n:ℤ) ∧ μ (free+1)=(A.length:ℤ) ∧
    μ (free+2)=(bv free n:ℤ) ∧ μ (free+3)=(B.length:ℤ) ∧
    μ (free+4)=(cv free n:ℤ) ∧ μ (free+5)=(C.length:ℤ) ∧
    μ (free+6)=(work free n:ℤ) := by sorry
