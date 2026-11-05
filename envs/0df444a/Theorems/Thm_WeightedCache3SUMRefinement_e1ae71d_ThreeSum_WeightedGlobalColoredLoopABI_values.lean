-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopABI_values
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopABI.values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:51:12.125796+00:00
-- url     : https://prove2.me/theorems/32e68092-0ff2-45da-974f-8c7d74713818
-- title:
--   values
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L18-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L18-L30

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopABI
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaLoop LightWeightedGlobalColoredSolver WeightedGlobalLocalParameters
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 1500000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopABI.values (S : Setup p m F K N E) (loc μ : ℕ→ℤ) (header : ℕ)
    (h5 : loc 5=(header:ℤ)) (h6 : loc 6=(S.input.free:ℤ))
    (h8 : loc 8=(addr S.input.free S.input.capacity 2:ℤ))
    (h9 : loc 9=(addr S.input.free S.input.capacity 3:ℤ))
    (h10 : loc 10=(addr S.input.free S.input.capacity 1:ℤ))
    (h11 : loc 11=(addr S.input.free S.input.capacity 13:ℤ))
    (hR : μ (header+15)=(S.rounds:ℤ)) (hJ : μ (header+16)=(S.arrays.J:ℤ)) :
    (loopArgs m F p (fixedAlpha m 2) (WeightedGlobalArenaSourceSetup.alphaRank m)
      (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.alpha S.beta S.budgetScale).map
        (fun e=>e.val ⟨loc,μ⟩)=S.initArgs := by sorry
