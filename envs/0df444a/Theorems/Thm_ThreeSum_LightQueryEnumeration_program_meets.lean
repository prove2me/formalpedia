-- Prove2me | Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
-- name    : ThreeSum.LightQueryEnumeration.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:02.755702+00:00
-- url     : https://prove2.me/theorems/939dbfa2-e823-4f66-8bd5-291563fb3d71
-- title:
--   Light Query Enumeration: program meets
-- statement:
--   The Light Query Enumeration construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryEnumeration.lean#L77-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryEnumeration.lean#L77-L90

import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightQueryEnumeration.program_meets {μ : ℕ → ℤ} {W t dst work d : ℕ}
    (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdst : dst+Q.card.choose t ≤ work)
    (hd : d+W+2 ≤ lim.depth) :
    Meets lim program 0 d [W,subsetMask Q,t,dst,work] μ (time W Q.card t)
      (fun r μ' => r = (Q.card.choose t : ℤ) ∧
        SegN μ' dst ((missingSets Q t).map subsetMask) ∧
        LightWeightedEnumeration.Weights μ' work Q.card (weights Q) ∧
        KeptBut μ μ' work dst (Q.card.choose t)) := by sorry
