-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEnumerationSetup_program_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEnumerationSetup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:24:34.153589+00:00
-- url     : https://prove2.me/theorems/91b9a8e2-be35-4bd4-a4b2-40080e4e3707
-- title:
--   program_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EnumerationSetup.lean#L80-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/EnumerationSetup.lean#L80-L91

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EnumerationSetup
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_program_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEnumerationSetup
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEnumerationSetup.program_meets {μ : ℕ → ℤ} {N T dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*N+1) ≤ lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((2740*N+3000 : ℕ) : ℤ)≤lim.word)
    (hcut : T ≤ 2740*N) (hdst : dst+(codes N T).length ≤ work)
    (hd : d+N+2 ≤ lim.depth) :
    Meets lim program 0 d [N,T,dst,work] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst ((codes N T).map (fun (a : ℕ) => (a : ℤ))) ∧
        Powers μ' work (2*N) ∧ KeptBut μ μ' work dst (codes N T).length) := by sorry
