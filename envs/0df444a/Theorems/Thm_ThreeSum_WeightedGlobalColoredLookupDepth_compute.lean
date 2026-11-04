-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLookupDepth_compute
-- name    : ThreeSum.WeightedGlobalColoredLookupDepth.compute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:20:36.775201+00:00
-- url     : https://prove2.me/theorems/84852764-ad84-4fec-bc68-f7bead4c0ef3
-- title:
--   Weighted Global Colored Lookup Depth: compute
-- statement:
--   The Weighted Global Colored Lookup Depth construction uses the compute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLookupDepth.lean#L14-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLookupDepth.lean#L14-L49

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLookupDepth
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColoredLookupDepth
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalColoredLookupDepth.compute {lim : Limits} {P : Program} {d header len r : ℕ}
    (loc μ : ℕ→ℤ) (hloc : loc 5=(header : ℤ))
    (hread : μ (header+15)=(r : ℤ)) (hspace : header+16≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word)
    (hword : ((len+2*len*r+16 : ℕ) : ℤ)≤lim.word) :
    Ends lim P d (.set 13 (k len *' H 15) ;; .set 14 (k 2 *' v 13)) ⟨loc,μ⟩ 11
      (fun σ=>σ.loc 13=(len*r : ℕ) ∧ σ.loc 14=(2*(len*r) : ℕ) ∧
        (∀i,i≠13→i≠14→σ.loc i=loc i) ∧ σ.mem=μ) := by sorry
