-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_of_ne_6de922e60143
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_of_ne_6de922e60143
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:05.225426+00:00
-- url     : https://prove2.me/theorems/88285a1f-7dcb-416c-9950-204439ca80f9
-- title:
--   P2 M Ground Theory Heights  Heights Log Int scale in Group apply of ne 6de922e60143: P2 M Ground Theory Heights  Heights Log Int scale in Group apply of ne 6de922e60143
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int scale in Group apply of ne 6de922e60143 construction uses the P2 M Ground Theory Heights  Heights Log Int scale in Group apply of ne 6de922e60143 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L102-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_of_ne_6de922e60143 (i a : Fin k) (ha : a ≠ i) (c : ℂ) (u : Fin k × Fin n → ℂ) (j : Fin n) :
    scaleP (inGroup i) c u (a, j) = u (a, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«scale_inGroup_apply_of_ne» := P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_of_ne_6de922e60143
