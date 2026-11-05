-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLookupDepth_compute
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLookupDepth.compute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:16.912299+00:00
-- url     : https://prove2.me/theorems/73b4be25-cfee-42e1-9255-4bce656e3657
-- title:
--   compute
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLookupDepth.lean#L14-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLookupDepth.lean#L14-L49

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPostABI
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLookupDepth
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLookupDepth
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 1000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLookupDepth.compute {lim : Limits} {P : Program} {d header len r : ℕ}
    (loc μ : ℕ→ℤ) (hloc : loc 5=(header : ℤ))
    (hread : μ (header+15)=(r : ℤ)) (hspace : header+16≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word)
    (hword : ((len+2*len*r+16 : ℕ) : ℤ)≤lim.word) :
    Ends lim P d (.set 13 (k len *' H 15) ;; .set 14 (k 2 *' v 13)) ⟨loc,μ⟩ 11
      (fun σ=>σ.loc 13=(len*r : ℕ) ∧ σ.loc 14=(2*(len*r) : ℕ) ∧
        (∀i,i≠13→i≠14→σ.loc i=loc i) ∧ σ.mem=μ) := by sorry
