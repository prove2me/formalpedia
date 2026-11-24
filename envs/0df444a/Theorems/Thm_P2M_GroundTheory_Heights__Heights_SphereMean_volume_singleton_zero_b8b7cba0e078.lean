-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_singleton_zero_b8b7cba0e078
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_volume_singleton_zero_b8b7cba0e078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:15.521099+00:00
-- url     : https://prove2.me/theorems/3d151e68-4664-41ba-bf82-6b4feda60ed5
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean volume singleton zero b8b7cba0e078: P2 M Ground Theory Heights  Heights Sphere Mean volume singleton zero b8b7cba0e078
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean volume singleton zero b8b7cba0e078 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean volume singleton zero b8b7cba0e078 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L73-L75

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_volume_singleton_zero_b8b7cba0e078 (m : ℕ) : volume ({0} : Set (Fin (m + 1) → ℂ)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«volume_singleton_zero» := P2M_GroundTheory_Heights__Heights_SphereMean_volume_singleton_zero_b8b7cba0e078
