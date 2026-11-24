-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_mul_polyP_51350dd3a25a
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_mul_polyP_51350dd3a25a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:52.758443+00:00
-- url     : https://prove2.me/theorems/6986917e-2148-4f4b-9e50-3ec4e26a1680
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean mul poly P 51350dd3a25a: P2 M Ground Theory Heights  Heights Sphere Mean mul poly P 51350dd3a25a
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean mul poly P 51350dd3a25a construction uses the P2 M Ground Theory Heights  Heights Sphere Mean mul poly P 51350dd3a25a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L20-L25

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_mul_polyP_51350dd3a25a (m : ℕ) (s : ℝ) : s * polyP m s = (1 - (1 - s) ^ (m + 1)) / (m + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«mul_polyP» := P2M_GroundTheory_Heights__Heights_SphereMean_mul_polyP_51350dd3a25a
