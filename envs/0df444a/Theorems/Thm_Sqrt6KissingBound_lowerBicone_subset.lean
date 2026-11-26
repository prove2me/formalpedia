-- Prove2me | Theorems.Thm_Sqrt6KissingBound_lowerBicone_subset
-- name    : Sqrt6KissingBound.lowerBicone_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T06:04:40.878953+00:00
-- url     : https://prove2.me/theorems/108ee0a7-a58a-4024-9980-403b583e8c39
-- title:
--   Sqrt6 Kissing Bound: lower Bicone subset
-- statement:
--   The Sqrt6 Kissing Bound construction uses the lower Bicone subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L124-L133
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L124-L133

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.lowerBicone_subset (k : ℕ) :
    lowerBicone k ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by sorry
