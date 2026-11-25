-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_norm_pos_9178f4bb2177
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_norm_pos_9178f4bb2177
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:11.318202+00:00
-- url     : https://prove2.me/theorems/ad12bd22-6fcc-4b1a-8eab-29832bc22cc5
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm norm pos 9178f4bb2177: P2 M Ground Theory Heights  Heights Herm Norm norm pos 9178f4bb2177
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm norm pos 9178f4bb2177 construction uses the P2 M Ground Theory Heights  Heights Herm Norm norm pos 9178f4bb2177 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L189-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L189-L200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
open Matrix

theorem P2M_GroundTheory_Heights__Heights_HermNorm_norm_pos_9178f4bb2177 (h : HermNorm n) {v : Fin n → ℂ} (hv : v ≠ 0) : 0 < h.norm v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«norm_pos» := P2M_GroundTheory_Heights__Heights_HermNorm_norm_pos_9178f4bb2177
