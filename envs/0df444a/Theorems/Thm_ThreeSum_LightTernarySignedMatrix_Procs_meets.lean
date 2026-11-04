-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_meets
-- name    : ThreeSum.LightTernarySignedMatrix.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:37:03.899303+00:00
-- url     : https://prove2.me/theorems/b34dbf34-8f2a-42c8-a727-20f05182377d
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedMatrix.lean#L60-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedMatrix.lean#L60-L140

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySignedMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernarySignedMatrix.Procs.meets {pMain : ℕ} {right : Bool} (C : Procs P pMain right)
    {μ : ℕ → ℤ} {src n U J radix dst work : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hb : 1 ≤ radix) (hsrc : src+n ≤ dst) (hsep : dst+n*(J+2) ≤ work)
    (hspace : space work U ≤ lim.space) (hword : (word U radix J : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hvalues : ∀ i < n, |f i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,U,J,radix,dst,work] μ (time n J U)
      (fun _ ν => Rows ν dst n J (fun i => raw right U radix J (f i)) ∧ Kept μ ν dst) := by sorry
