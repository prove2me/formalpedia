-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_primG_eq_646b67a09f3a
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_primG_eq_646b67a09f3a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:51.061733+00:00
-- url     : https://prove2.me/theorems/cae5a925-b07f-5a9d-a585-88779a1431fc
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean prim G eq 646b67a09f3a: P2 M Ground Theory Heights  Heights Sphere Mean prim G eq 646b67a09f3a
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean prim G eq 646b67a09f3a construction uses the P2 M Ground Theory Heights  Heights Sphere Mean prim G eq 646b67a09f3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L44-L46

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_primG_eq_646b67a09f3a (m : ℕ) (s : ℝ) : primG m s = polyP m s * (s * log s) - polyR m s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«primG_eq» := P2M_GroundTheory_Heights__Heights_SphereMean_primG_eq_646b67a09f3a
