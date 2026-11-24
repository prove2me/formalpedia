-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurable_sqNorm_950a20036208
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_measurable_sqNorm_950a20036208
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:39.790056+00:00
-- url     : https://prove2.me/theorems/2b1edcf4-dddd-42f8-aabe-de0e2e6ef711
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean measurable sq Norm 950a20036208: P2 M Ground Theory Heights  Heights Sphere Mean measurable sq Norm 950a20036208
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean measurable sq Norm 950a20036208 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean measurable sq Norm 950a20036208 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L59-L60

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_measurable_sqNorm_950a20036208 (n : ℕ) : Measurable (sqNorm (n := n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«measurable_sqNorm» := P2M_GroundTheory_Heights__Heights_SphereMean_measurable_sqNorm_950a20036208
