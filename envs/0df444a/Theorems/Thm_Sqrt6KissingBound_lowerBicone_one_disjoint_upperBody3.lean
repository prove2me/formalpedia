-- Prove2me | Theorems.Thm_Sqrt6KissingBound_lowerBicone_one_disjoint_upperBody3
-- name    : Sqrt6KissingBound.lowerBicone_one_disjoint_upperBody3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:14:58.7812+00:00
-- url     : https://prove2.me/theorems/ae1438e0-ee4b-5770-a5b3-40bafdd4ec67
-- title:
--   Sqrt6 Kissing Bound: lower Bicone one disjoint upper Body3
-- statement:
--   The Sqrt6 Kissing Bound construction uses the lower Bicone one disjoint upper Body3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L73-L78
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L73-L78

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real

theorem Sqrt6KissingBound.lowerBicone_one_disjoint_upperBody3 : Disjoint (lowerBicone 1) upperBody3 := by sorry
