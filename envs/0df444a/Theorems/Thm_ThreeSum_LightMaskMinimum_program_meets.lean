-- Prove2me | Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
-- name    : ThreeSum.LightMaskMinimum.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:25:28.293989+00:00
-- url     : https://prove2.me/theorems/deb73162-4d4b-4124-835e-3adc3ef5ce2e
-- title:
--   Light Mask Minimum: program meets
-- statement:
--   The Light Mask Minimum construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskMinimum.lean#L135-L143
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskMinimum.lean#L135-L143

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskMinimum
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightMaskMinimum.program_meets {μ : ℕ → ℤ} {L work d : ℕ}
    (S : Finset (Fin L)) (hS : S.Nonempty)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,subsetMask S,work] μ (time L)
      (fun r μ' => r = ((S.min' hS).val : ℤ) ∧ Kept μ μ' work) := by sorry
