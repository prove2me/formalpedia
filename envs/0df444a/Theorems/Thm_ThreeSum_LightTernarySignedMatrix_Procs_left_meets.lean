-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_left_meets
-- name    : ThreeSum.LightTernarySignedMatrix.Procs.left_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:45:14.255382+00:00
-- url     : https://prove2.me/theorems/edd3f692-041b-4ec4-8900-d2239de68d73
-- title:
--   Procs: left meets
-- statement:
--   The Procs construction uses the left meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedMatrix.lean#L142-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedMatrix.lean#L142-L150

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_left_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySignedMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernarySignedMatrix.Procs.left_meets {pMain : ℕ} (C : Procs P pMain false)
    {μ : ℕ → ℤ} {src n U J radix dst work : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hb : 1 ≤ radix) (hsrc : src+n ≤ dst) (hsep : dst+n*(J+2) ≤ work)
    (hspace : space work U ≤ lim.space) (hword : (word U radix J : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hvalues : ∀ i < n, |f i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,U,J,radix,dst,work] μ (time n J U)
      (fun _ ν => Rows ν dst n J (fun i => leftRaw U radix J (f i)) ∧ Kept μ ν dst) := by sorry
