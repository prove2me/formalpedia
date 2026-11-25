-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_sum_mul_pointOf_e015eaf40c49
-- name    : P2M_GroundTheory_Heights__Heights_ConeFsLog_sum_mul_pointOf_e015eaf40c49
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:45.385652+00:00
-- url     : https://prove2.me/theorems/be8ec5e6-64f4-4373-a5c6-4d2504bec37e
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fs Log sum mul point Of e015eaf40c49: P2 M Ground Theory Heights  Heights Cone Fs Log sum mul point Of e015eaf40c49
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fs Log sum mul point Of e015eaf40c49 construction uses the P2 M Ground Theory Heights  Heights Cone Fs Log sum mul point Of e015eaf40c49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L22-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
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
open MvPolynomial MeasureTheory Set Matrix Filter
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFsLog
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeFsLog_sum_mul_pointOf_e015eaf40c49 (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf y j = ∑ i, (h.mat *ᵥ u) i * y i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFsLog».«sum_mul_pointOf» := P2M_GroundTheory_Heights__Heights_ConeFsLog_sum_mul_pointOf_e015eaf40c49
