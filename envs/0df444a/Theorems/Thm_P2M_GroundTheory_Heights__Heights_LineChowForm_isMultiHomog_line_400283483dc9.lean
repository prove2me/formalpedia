-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isMultiHomog_line_400283483dc9
-- name    : P2M_GroundTheory_Heights__Heights_LineChowForm_isMultiHomog_line_400283483dc9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:49.321582+00:00
-- url     : https://prove2.me/theorems/35856419-19ee-4581-b4ba-68e4b0cac8ae
-- title:
--   P2 M Ground Theory Heights  Heights Line Chow Form is Multi Homog line 400283483dc9: P2 M Ground Theory Heights  Heights Line Chow Form is Multi Homog line 400283483dc9
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Chow Form is Multi Homog line 400283483dc9 construction uses the P2 M Ground Theory Heights  Heights Line Chow Form is Multi Homog line 400283483dc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L186-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L186-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_LineChowForm_isMultiHomog_line_400283483dc9 : IsMultiHomog 1 (D2 : MvPolynomial (Fin 2 × Fin 2) F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineChowForm».«isMultiHomog_line» := P2M_GroundTheory_Heights__Heights_LineChowForm_isMultiHomog_line_400283483dc9
