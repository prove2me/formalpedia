-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopABI_values
-- name    : ThreeSum.WeightedGlobalColoredLoopABI.values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:07:49.138571+00:00
-- url     : https://prove2.me/theorems/82c4b9c1-ac31-49be-8fc0-4fa1c3df21d0
-- title:
--   Weighted Global Colored Loop ABI: values
-- statement:
--   The Weighted Global Colored Loop ABI construction uses the values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L18-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L18-L30

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaLoop LightWeightedGlobalColoredSolver WeightedGlobalLocalParameters
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 1500000

theorem ThreeSum.WeightedGlobalColoredLoopABI.values (S : Setup p m F K N E) (loc μ : ℕ→ℤ) (header : ℕ)
    (h5 : loc 5=(header:ℤ)) (h6 : loc 6=(S.input.free:ℤ))
    (h8 : loc 8=(addr S.input.free S.input.capacity 2:ℤ))
    (h9 : loc 9=(addr S.input.free S.input.capacity 3:ℤ))
    (h10 : loc 10=(addr S.input.free S.input.capacity 1:ℤ))
    (h11 : loc 11=(addr S.input.free S.input.capacity 13:ℤ))
    (hR : μ (header+15)=(S.rounds:ℤ)) (hJ : μ (header+16)=(S.arrays.J:ℤ)) :
    (loopArgs m F p (fixedAlpha m 2) (WeightedGlobalArenaSourceSetup.alphaRank m)
      (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.alpha S.beta S.budgetScale).map
        (fun e=>e.val ⟨loc,μ⟩)=S.initArgs := by sorry
