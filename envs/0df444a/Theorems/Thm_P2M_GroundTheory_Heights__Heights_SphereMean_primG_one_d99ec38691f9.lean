-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_primG_one_d99ec38691f9
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_primG_one_d99ec38691f9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:20.767464+00:00
-- url     : https://prove2.me/theorems/1aa1c839-3d45-40df-a45f-a02d71f2799f
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean prim G one d99ec38691f9: P2 M Ground Theory Heights  Heights Sphere Mean prim G one d99ec38691f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean prim G one d99ec38691f9 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean prim G one d99ec38691f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L83-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_primG_one_d99ec38691f9 (m : ℕ) : primG m 1 = -(harmonic (m + 1) : ℝ) / (m + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«primG_one» := P2M_GroundTheory_Heights__Heights_SphereMean_primG_one_d99ec38691f9
