-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryApply_meets
-- name    : ThreeSum.LightTernaryCarryApply.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:37:18.940765+00:00
-- url     : https://prove2.me/theorems/2e3096ee-645a-4d44-b4c7-bc2f9984ed0b
-- title:
--   Light Ternary Carry Apply: meets
-- statement:
--   The Light Ternary Carry Apply construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryApply.lean#L20-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryApply.lean#L20-L121

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryApply
open Light TernarySignedDigits TernarySignedReduction TernarySignedModes
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryCarryApply.meets {pMain pLinear : ℕ}
    (hmain : P[pMain]?=some (body pLinear))
    (hlinear : P[pLinear]?=some LightArray.linearBody)
    {μ : ℕ→ℤ} {U radix J dst carry : ℕ} (a : ℤ) (c : CarryWord J)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth) (hb : 1<radix)
    (hsep : carry+J+1≤dst ∨ dst+J+2≤carry)
    (hspace : max (carry+J+1) (dst+J+2)≤lim.space)
    (hword : (4*(radix : ℤ)+8)≤lim.word)
    (hA : ∀ k<J, μ (dst+k)=(digit radix (shiftOne U a) (J-1-k) : ℤ))
    (hcarry : ∀ k≤J, μ (carry+k)=carryAt c (J-k))
    (ht0 : μ (dst+J)=1) (ht1 : μ (dst+J+1)=1) :
    Meets lim P pMain d [dst,carry,J,radix] μ (time J)
      (fun _ ν => LightTernarySignedRow.Row ν dst J (requesterRaw U radix J a c) ∧
        Kept μ ν dst) := by sorry
