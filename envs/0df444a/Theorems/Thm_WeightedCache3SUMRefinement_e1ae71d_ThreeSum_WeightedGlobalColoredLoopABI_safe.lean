-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopABI_safe
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopABI.safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:54:51.721944+00:00
-- url     : https://prove2.me/theorems/7bf02322-ea69-45c3-bc0d-d52bdb3374c4
-- title:
--   safe
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L36-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopABI.lean#L36-L53

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopABI
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaLoop LightWeightedGlobalColoredSolver WeightedGlobalLocalParameters
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 1500000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopABI.safe {lim : Limits} (S : Setup p m F K N E) (loc μ : ℕ→ℤ) (header : ℕ)
    (h5 : loc 5=(header:ℤ)) (hheader : header+17≤lim.space)
    (hw : (lim.space:ℤ)≤lim.word) (hs : (scalar S:ℤ)≤lim.word) :
    ∀e∈loopArgs m F p (fixedAlpha m 2) (WeightedGlobalArenaSourceSetup.alphaRank m)
      (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.alpha S.beta S.budgetScale,
      e.Safe lim ⟨loc,μ⟩ := by sorry
