-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_af9c6325d276
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_af9c6325d276
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:09.782274+00:00
-- url     : https://prove2.me/theorems/967ffc15-3545-4286-b43d-38f7f65ce221
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set af9c6325d276: P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set af9c6325d276
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set af9c6325d276 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set af9c6325d276 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L82-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_af9c6325d276 {n : ℕ} {s : ℝ} (hs : 0 < s) :
    volume (ballSet n s) = ENNReal.ofReal (s ^ n) * volume (ballSet n 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«volume_ballSet» := P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_af9c6325d276
