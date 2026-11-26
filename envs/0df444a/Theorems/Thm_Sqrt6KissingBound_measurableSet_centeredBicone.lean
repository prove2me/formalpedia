-- Prove2me | Theorems.Thm_Sqrt6KissingBound_measurableSet_centeredBicone
-- name    : Sqrt6KissingBound.measurableSet_centeredBicone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:13:15.759822+00:00
-- url     : https://prove2.me/theorems/00e244a6-2822-4034-b660-6ad687a94592
-- title:
--   Sqrt6 Kissing Bound: measurable Set centered Bicone
-- statement:
--   The Sqrt6 Kissing Bound construction uses the measurable Set centered Bicone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean#L32-L35
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean#L32-L35

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.measurableSet_centeredBicone (k : ℕ)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    MeasurableSet (centeredBicone k x) := by sorry
