-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fsLog_le_a8984c2e2088
-- name    : P2M_GroundTheory_Heights__Heights_fsLog_le_a8984c2e2088
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:12.015553+00:00
-- url     : https://prove2.me/theorems/eb11547a-beaf-56ef-8531-17a7a3423054
-- title:
--   P2 M Ground Theory Heights  Heights fs Log le a8984c2e2088: P2 M Ground Theory Heights  Heights fs Log le a8984c2e2088
-- statement:
--   The P2 M Ground Theory Heights  Heights fs Log le a8984c2e2088 construction uses the P2 M Ground Theory Heights  Heights fs Log le a8984c2e2088 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L46-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
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
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_fsLog_le_a8984c2e2088 (h : HermNorm n) {u y : Fin n → ℂ} (hy : ∑ j, u j * y j ≠ 0) :
    fsLog h u y ≤ Real.log (h.norm u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fsLog_le» := P2M_GroundTheory_Heights__Heights_fsLog_le_a8984c2e2088
