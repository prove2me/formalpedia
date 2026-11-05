-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredPrefixCall_lift
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPrefixCall.lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:38:42.147563+00:00
-- url     : https://prove2.me/theorems/a825e83a-ef1c-4462-b924-4841c46f2a89
-- title:
--   lift
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPrefixCall.lean#L19-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPrefixCall.lean#L19-L34

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPrefixCall
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPrefixCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 1500000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPrefixCall.lift {lim : Limits} {radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (post : Program) (postMain : ℕ) {entry depth T : ℕ} {args : List ℤ}
    {μ : ℕ→ℤ} {Q : ℤ→(ℕ→ℤ)→Prop}
    (h : Meets lim (LightWeightedGlobalPrefixLoop.program p R F K raws words maps xl yl zl xr yr zr)
      entry depth args μ T Q) :
    Meets lim (program radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L
      raws words maps xl yl zl xr yr zr post postMain) (55+entry) depth args μ T Q := by sorry
