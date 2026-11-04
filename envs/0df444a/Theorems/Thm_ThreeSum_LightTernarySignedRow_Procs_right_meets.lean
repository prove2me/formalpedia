-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_right_meets
-- name    : ThreeSum.LightTernarySignedRow.Procs.right_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:19.235772+00:00
-- url     : https://prove2.me/theorems/c78b9b66-4b5f-4917-8735-21c968f0063b
-- title:
--   Procs: right meets
-- statement:
--   The Procs construction uses the right meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedRow.lean#L135-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedRow.lean#L135-L156

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

theorem ThreeSum.LightTernarySignedRow.Procs.right_meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {J radix dst work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth) (hb : 1≤radix)
    (hC : |c|≤(U : ℤ)) (hsep : dst+J+2≤work)
    (hspace : space work (3*U)≤lim.space) (hword : (word (3*U) radix J : ℤ)≤lim.word) :
    Meets lim P pMain d [c,2*U,1,J,radix,dst,work,0,1] μ (time J (3*U))
      (fun _ ν => Row ν dst J (rightRaw U radix J c) ∧ Kept μ ν dst) := by sorry
