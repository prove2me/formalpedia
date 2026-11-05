-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixHeader_stores_ends
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader.stores_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:02:24.469674+00:00
-- url     : https://prove2.me/theorems/44c648fd-e151-4964-9bad-26a940478986
-- title:
--   stores_ends
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L20-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L20-L40

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixHeader
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_stores_ends

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader.stores_ends {lim : Limits} {P : Program} {d base : ℕ}
    (fs : List (ℕ×ℕ)) (loc μ : ℕ→ ℤ)
    (hbase : loc 1=(base:ℤ)) (hw : (lim.space:ℤ)≤lim.word)
    (hspace : base+106≤lim.space)
    (hgood : ∀ ir∈fs, ir.1<106 ∧ |loc ir.2|≤lim.word) :
    Ends lim P d (stores fs) ⟨loc,μ⟩ (10*fs.length)
      (fun σ=>σ.loc=loc ∧ σ.mem=patch base loc μ fs) := by sorry
