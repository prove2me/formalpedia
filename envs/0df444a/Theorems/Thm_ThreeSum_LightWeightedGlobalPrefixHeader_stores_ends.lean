-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_stores_ends
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.stores_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:42:21.971605+00:00
-- url     : https://prove2.me/theorems/ee597227-d928-4875-bc74-1aa8fcb54fb2
-- title:
--   Light Weighted Global Prefix Header: stores ends
-- statement:
--   The Light Weighted Global Prefix Header construction uses the stores ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L20-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L20-L40

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_stores_ends

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.stores_ends {lim : Limits} {P : Program} {d base : ℕ}
    (fs : List (ℕ×ℕ)) (loc μ : ℕ→ ℤ)
    (hbase : loc 1=(base:ℤ)) (hw : (lim.space:ℤ)≤lim.word)
    (hspace : base+106≤lim.space)
    (hgood : ∀ ir∈fs, ir.1<106 ∧ |loc ir.2|≤lim.word) :
    Ends lim P d (stores fs) ⟨loc,μ⟩ (10*fs.length)
      (fun σ=>σ.loc=loc ∧ σ.mem=patch base loc μ fs) := by sorry
