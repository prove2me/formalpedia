-- Prove2me | Theorems.Thm_Sqrt6KissingBound_lowerBicone_disjoint_upperBicone
-- name    : Sqrt6KissingBound.lowerBicone_disjoint_upperBicone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:12:00.543604+00:00
-- url     : https://prove2.me/theorems/2b0e7a2a-7c50-429f-9101-59b7fcc7cf31
-- title:
--   Sqrt6 Kissing Bound: lower Bicone disjoint upper Bicone
-- statement:
--   The Sqrt6 Kissing Bound construction uses the lower Bicone disjoint upper Bicone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L152-L163
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L152-L163

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.lowerBicone_disjoint_upperBicone (k : ℕ) :
    Disjoint (lowerBicone k) (upperBicone k) := by sorry
