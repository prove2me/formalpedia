-- Prove2me | Theorems.Thm_Sqrt6KissingBound_centeredBicone_disjoint
-- name    : Sqrt6KissingBound.centeredBicone_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:12:35.021643+00:00
-- url     : https://prove2.me/theorems/d5002c7c-b5af-5983-baee-ff2c6e8320f2
-- title:
--   Sqrt6 Kissing Bound: centered Bicone disjoint
-- statement:
--   The Sqrt6 Kissing Bound construction uses the centered Bicone disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean#L72-L79
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean#L72-L79

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.centeredBicone_disjoint {k : ℕ}
    {x z : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (centeredBicone k x) (centeredBicone k z) := by sorry
