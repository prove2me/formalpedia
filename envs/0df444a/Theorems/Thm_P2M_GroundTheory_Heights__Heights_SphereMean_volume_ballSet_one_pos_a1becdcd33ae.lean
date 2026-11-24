-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_pos_a1becdcd33ae
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_pos_a1becdcd33ae
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:18.692811+00:00
-- url     : https://prove2.me/theorems/ffa5508a-19be-4be7-b829-c2d2d058fcb9
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set one pos a1becdcd33ae: P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set one pos a1becdcd33ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set one pos a1becdcd33ae construction uses the P2 M Ground Theory Heights  Heights Sphere Mean volume ball Set one pos a1becdcd33ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L99-L100

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_pos_a1becdcd33ae (n : ℕ) : 0 < volume (ballSet n 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«volume_ballSet_one_pos» := P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_pos_a1becdcd33ae
