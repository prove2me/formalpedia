-- Prove2me | Theorems.Thm_ThreeSum_LightColorParameters_program_meets
-- name    : ThreeSum.LightColorParameters.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:15.271933+00:00
-- url     : https://prove2.me/theorems/b433a26d-5e1f-4c59-b28b-faaddea7e69b
-- title:
--   Light Color Parameters: program meets
-- statement:
--   The Light Color Parameters construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorParameters.lean#L133-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorParameters.lean#L133-L137

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Theorems.Thm_ThreeSum_LightClassFilter_program_meets
import Theorems.Thm_ThreeSum_LightColorIndex_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorParameters
open Light ColorParameters
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d W t free : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightColorParameters.program_meets (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+6 ≤ lim.space)
    (hword : ((t+W+10 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [W,t,free] μ (time t)
      (fun result ν => result=(free : ℤ) ∧ Seg ν free (data W t) ∧ SameOutside μ ν free 6) := by sorry
