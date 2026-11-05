-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeMomentBounds_factorial_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.factorial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:22:14.436534+00:00
-- url     : https://prove2.me/theorems/ce8c255e-a294-4c47-8dcd-812956afa0c7
-- title:
--   factorial_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L52-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L52-L62

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.factorial_le {N : ℕ} (Q : TritWord N) : TernaryConvolution.factorial Q≤(2 : ℤ)^N := by sorry
