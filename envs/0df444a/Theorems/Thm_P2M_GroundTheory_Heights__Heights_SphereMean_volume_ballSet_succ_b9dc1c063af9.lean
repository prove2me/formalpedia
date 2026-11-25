-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_succ_b9dc1c063af9
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_succ_b9dc1c063af9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:19.31072+00:00
-- url     : https://prove2.me/theorems/9185e4ef-eb22-45b6-a146-a34d7247d685
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set succ b9dc1c063af9: P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set succ b9dc1c063af9
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set succ b9dc1c063af9 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set succ b9dc1c063af9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L77-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L77-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_succ_b9dc1c063af9 (m : ℕ) :
    volume (ballSet (m + 1) 1) = ENNReal.ofReal (π / (m + 1)) * volume (ballSet m 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«volume_ballSet_succ» := P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_succ_b9dc1c063af9
