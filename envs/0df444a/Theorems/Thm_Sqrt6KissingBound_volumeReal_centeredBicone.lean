-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volumeReal_centeredBicone
-- name    : Sqrt6KissingBound.volumeReal_centeredBicone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:12:31.793319+00:00
-- url     : https://prove2.me/theorems/80969ccc-6a30-5e8b-b889-4eb97fd609a5
-- title:
--   Sqrt6 Kissing Bound: volume Real centered Bicone
-- statement:
--   The Sqrt6 Kissing Bound construction uses the volume Real centered Bicone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean#L37-L46
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean#L37-L46

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.volumeReal_centeredBicone (k : ℕ)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real
        (centeredBicone k x) =
      (1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1) := by sorry
