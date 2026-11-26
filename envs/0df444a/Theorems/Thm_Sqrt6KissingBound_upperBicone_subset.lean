-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upperBicone_subset
-- name    : Sqrt6KissingBound.upperBicone_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:04:38.006285+00:00
-- url     : https://prove2.me/theorems/98d3e50d-a024-4b4a-bad4-67765158fc7d
-- title:
--   Sqrt6 Kissing Bound: upper Bicone subset
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper Bicone subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L135-L146
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L135-L146

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.upperBicone_subset (k : ℕ) :
    upperBicone k ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by sorry
