-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalDigitLength_clog_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDigitLength.clog_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:22:30.919982+00:00
-- url     : https://prove2.me/theorems/d7b88f20-d26f-43f9-af3b-1834e97048a8
-- title:
--   clog_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDigitLength.lean#L28-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDigitLength.lean#L28-L68

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDigitLength
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDigitLength
open Light WeightedGlobalSignedPadding
variable {lim : Limits} {P : Program} {d : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDigitLength.clog_meets {p b x : ℕ} (hp : P[p]?=some clogBody) (μ : ℕ→ℤ)
    (hb : 1<b) (hx : 0<x) (hword : (word b x : ℤ)≤lim.word) :
    Meets lim P p d [x,b] μ (clogTime b x)
      (fun r ν => r=(Nat.clog b x : ℤ) ∧ ν=μ) := by sorry
