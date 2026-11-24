-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:33.456893+00:00
-- url     : https://prove2.me/theorems/b0fb436f-a384-4ebb-8ea3-b079eb5973dc
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean sq Norm nonneg b8444e370306: P2 M Ground Theory Heights  Heights Sphere Mean sq Norm nonneg b8444e370306
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean sq Norm nonneg b8444e370306 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean sq Norm nonneg b8444e370306 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L52-L53

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306 {n : ℕ} (x : Fin n → ℂ) : 0 ≤ sqNorm x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«sqNorm_nonneg» := P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306
