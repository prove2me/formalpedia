-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_left_meets
-- name    : ThreeSum.LightTernarySignedRow.Procs.left_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:19:59.190194+00:00
-- url     : https://prove2.me/theorems/faa7c0f4-dbe4-4e21-8bef-7271a59e69af
-- title:
--   Procs: left meets
-- statement:
--   The Procs construction uses the left meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedRow.lean#L112-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedRow.lean#L112-L133

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySignedRow
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernarySignedRow.Procs.left_meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {J radix dst work U : ℕ} {b : ℤ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth) (hb : 1≤radix)
    (hB : |b|≤(U : ℤ)) (hsep : dst+J+2≤work)
    (hspace : space work (3*U)≤lim.space) (hword : (word (3*U) radix J : ℤ)≤lim.word) :
    Meets lim P pMain d [b,U,-1,J,radix,dst,work,1,0] μ (time J (3*U))
      (fun _ ν => Row ν dst J (leftRaw U radix J b) ∧ Kept μ ν dst) := by sorry
