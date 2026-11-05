-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_program_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:03.072998+00:00
-- url     : https://prove2.me/theorems/2712c4d6-d0bb-459a-b8ca-d23309ce422a
-- title:
--   program_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean#L273-L284
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean#L273-L284

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.program_meets {W powers N T pref dst d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((2740*W+3000 : ℕ) : ℤ) ≤ lim.word)
    (hN : N ≤ W) (hT : T ≤ 2740*W) (hprefix : pref+4^N ≤ 4^W)
    (hdst : dst+(codes N T).length ≤ powers) (hpowers : Powers μ powers (2*W))
    (hd : d+N ≤ lim.depth) :
    Meets lim program 0 d [N,T,pref,dst,powers] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst (output N T pref) ∧ SameOutside μ μ' dst (codes N T).length) := by sorry
