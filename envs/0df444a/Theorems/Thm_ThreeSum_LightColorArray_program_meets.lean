-- Prove2me | Theorems.Thm_ThreeSum_LightColorArray_program_meets
-- name    : ThreeSum.LightColorArray.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:01.275324+00:00
-- url     : https://prove2.me/theorems/09ecc6e9-a406-454a-a032-f18d5c4bf092
-- title:
--   Light Color Array: program meets
-- statement:
--   The Light Color Array construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorArray.lean#L104-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorArray.lean#L104-L113

import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightColorArray
import Theorems.Thm_ThreeSum_LightColorIndex_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorArray
open Light LightSubsetAddress
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightColorArray.program_meets {W n dst work : ℕ} (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hdst : dst+n ≤ work) (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hd : d+W+2 ≤ lim.depth) :
    Meets lim program 0 d [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,dst,work]
      μ (time W n) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightColorIndex.color p i : ℤ)) ∧
        Powers ν work W ∧ KeptBut μ ν work dst n) := by sorry
