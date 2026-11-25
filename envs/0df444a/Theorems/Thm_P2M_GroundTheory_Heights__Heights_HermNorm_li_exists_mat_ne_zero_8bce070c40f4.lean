-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_mat_ne_zero_8bce070c40f4
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_mat_ne_zero_8bce070c40f4
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:19.246274+00:00
-- url     : https://prove2.me/theorems/51eae781-19fd-4e8c-8bb9-7e4242c33088
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm li exists mat ne zero 8bce070c40f4: P2 M Ground Theory Heights  Heights Herm Norm li exists mat ne zero 8bce070c40f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm li exists mat ne zero 8bce070c40f4 construction uses the P2 M Ground Theory Heights  Heights Herm Norm li exists mat ne zero 8bce070c40f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L66-L69

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
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_mat_ne_zero_8bce070c40f4 (h : HermNorm n) (l : Fin n) : ∃ j, h.mat l j ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«li_exists_mat_ne_zero» := P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_mat_ne_zero_8bce070c40f4
