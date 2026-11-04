-- Prove2me | Theorems.Thm_ThreeSum_LightNormalize_program_meets
-- name    : ThreeSum.LightNormalize.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:40.833948+00:00
-- url     : https://prove2.me/theorems/1b1e0c83-bdba-4df9-bf5b-211f9ca78157
-- title:
--   Light Normalize: program meets
-- statement:
--   The Light Normalize construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L177-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L177-L188

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightNormalize.program_meets {src dst work d : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hseg : Seg μ src L) (hsep : src+L.length ≤ dst)
    (hwork : dst+L.length ≤ work) (hspace : space work L.length ≤ lim.space)
    (hd : d+L.length+Nat.clog 2 L.length+2 ≤ lim.depth) :
    Meets lim program 0 d [src,L.length,dst,work] μ (time L.length)
      (fun r μ' => ∃ out : List ℤ,
        r = (out.length : ℤ) ∧ Seg μ' dst out ∧ out.Pairwise (· < ·) ∧
        out.length ≤ L.length ∧ (∀ z, z ∈ out ↔ z ∈ L) ∧
        ∀ a, a < work → (a < src ∨ src+L.length ≤ a) →
          (a < dst ∨ dst+L.length ≤ a) → μ' a = μ a) := by sorry
