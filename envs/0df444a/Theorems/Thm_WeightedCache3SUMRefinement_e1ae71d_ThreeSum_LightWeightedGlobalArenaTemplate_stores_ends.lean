-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalArenaTemplate_stores_ends
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalArenaTemplate.stores_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:29:00.546208+00:00
-- url     : https://prove2.me/theorems/63d6f5c8-fe05-4c75-8ae6-3a05de6d929e
-- title:
--   stores_ends
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L115-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L115-L166

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryArenaTemplate
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_stores_ends

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalArenaTemplate.stores_ends {lim : Limits} {P : Program} {depth free C dstSlot : ℕ}
    (fs : List Field) (offset : ℕ) (loc μ : ℕ → ℤ)
    (hfree : loc 1=(free : ℤ)) (hC : loc 24=(C : ℤ)) (hpos : 1≤C)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (hslot : dstSlot<67) (hspace : addr free C dstSlot+offset+fs.length≤lim.space)
    (hgood : ∀ f∈fs, Good f) (hsquare : |loc 16*loc 16|≤lim.word) :
    Ends lim P depth (stores dstSlot offset fs) ⟨loc,μ⟩ (20*fs.length)
      (fun σ => σ.loc=loc ∧
        Seg σ.mem (addr free C dstSlot+offset) (fs.map (value loc free C)) ∧
        SameOutside μ σ.mem (addr free C dstSlot+offset) fs.length) := by sorry
