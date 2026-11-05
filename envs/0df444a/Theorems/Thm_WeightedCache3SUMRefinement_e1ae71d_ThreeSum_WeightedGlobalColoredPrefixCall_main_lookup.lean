-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredPrefixCall_main_lookup
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPrefixCall.main_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:26.195264+00:00
-- url     : https://prove2.me/theorems/b0b539a5-4685-41e5-a4e3-9e20e2ecdfba
-- title:
--   main_lookup
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPrefixCall.lean#L36-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPrefixCall.lean#L36-L49

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPrefixCall.main_lookup (radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (post : Program) (postMain : ℕ) :
    (program radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L
      raws words maps xl yl zl xr yr zr post postMain)[252+post.length]?=
      some (body (252+postMain) m F p alpha2 alphaRank localQ R a b scaleBase L) := by sorry
