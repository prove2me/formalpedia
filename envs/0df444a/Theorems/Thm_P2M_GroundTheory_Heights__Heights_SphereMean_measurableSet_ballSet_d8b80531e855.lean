-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:54.618429+00:00
-- url     : https://prove2.me/theorems/4d0f8b83-14c9-4c68-badc-2260acf4f434
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean measurable Set ball Set d8b80531e855: P2 M Ground Theory Heights  Heights Sphere Mean measurable Set ball Set d8b80531e855
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean measurable Set ball Set d8b80531e855 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean measurable Set ball Set d8b80531e855 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L65-L66

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855 (n : ℕ) (s : ℝ) : MeasurableSet (ballSet n s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«measurableSet_ballSet» := P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
