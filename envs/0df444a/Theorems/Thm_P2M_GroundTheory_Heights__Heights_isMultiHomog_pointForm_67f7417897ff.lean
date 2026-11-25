-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_pointForm_67f7417897ff
-- name    : P2M_GroundTheory_Heights__Heights_isMultiHomog_pointForm_67f7417897ff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:48:52.589207+00:00
-- url     : https://prove2.me/theorems/1fb01bfa-ac76-52ae-84e5-1ccd72be1e7e
-- title:
--   P2 M Ground Theory Heights  Heights is Multi Homog point Form 67f7417897ff: P2 M Ground Theory Heights  Heights is Multi Homog point Form 67f7417897ff
-- statement:
--   The P2 M Ground Theory Heights  Heights is Multi Homog point Form 67f7417897ff construction uses the P2 M Ground Theory Heights  Heights is Multi Homog point Form 67f7417897ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDefectPoint.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDefectPoint.lean#L14-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectPoint
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isMultiHomog_pointForm_67f7417897ff (c : ℂ) (y : Fin n → ℂ) :
    IsMultiHomog 1 (C c * ∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isMultiHomog_pointForm» := P2M_GroundTheory_Heights__Heights_isMultiHomog_pointForm_67f7417897ff
