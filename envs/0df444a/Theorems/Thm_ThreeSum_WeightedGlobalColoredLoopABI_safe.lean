-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopABI_safe
-- name    : ThreeSum.WeightedGlobalColoredLoopABI.safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:14:47.695274+00:00
-- url     : https://prove2.me/theorems/1903abef-8d3a-4b85-b4d4-135f57391f05
-- title:
--   Weighted Global Colored Loop ABI: safe
-- statement:
--   The Weighted Global Colored Loop ABI construction uses the safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L36-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L36-L53

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaLoop LightWeightedGlobalColoredSolver WeightedGlobalLocalParameters
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 1500000

theorem ThreeSum.WeightedGlobalColoredLoopABI.safe {lim : Limits} (S : Setup p m F K N E) (loc μ : ℕ→ℤ) (header : ℕ)
    (h5 : loc 5=(header:ℤ)) (hheader : header+17≤lim.space)
    (hw : (lim.space:ℤ)≤lim.word) (hs : (scalar S:ℤ)≤lim.word) :
    ∀e∈loopArgs m F p (fixedAlpha m 2) (WeightedGlobalArenaSourceSetup.alphaRank m)
      (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.alpha S.beta S.budgetScale,
      e.Safe lim ⟨loc,μ⟩ := by sorry
