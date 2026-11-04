-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryOriginalRequester_Procs_meets
-- name    : ThreeSum.LightTernaryOriginalRequester.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:36.683914+00:00
-- url     : https://prove2.me/theorems/63637396-0356-4839-9d90-de7b9d0b8990
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalRequester.lean#L25-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalRequester.lean#L25-L77

import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryCarryApply_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryOriginalRequester
open Light TernarySignedDigits TernarySignedReduction
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryOriginalRequester.Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {U radix J dst carry work : ℕ} (a : ℤ) (c : CarryWord J)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+3<lim.depth) (hb : 1<radix)
    (hA : |a|≤(U : ℤ)) (hcarryBefore : carry+J+1≤dst) (hsep : dst+J+2≤work)
    (hspace : LightTernarySignedRow.space work (3*U)≤lim.space)
    (hword : (LightTernarySignedRow.word (3*U) radix J : ℤ)≤lim.word)
    (hcarry : ∀ k≤J, μ (carry+k)=carryAt c (J-k)) :
    Meets lim P pMain d [a,U,radix,J,dst,carry,work] μ (time J U)
      (fun _ ν => LightTernarySignedRow.Row ν dst J (requesterRaw U radix J a c) ∧
        Kept μ ν dst) := by sorry
