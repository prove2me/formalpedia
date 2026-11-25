-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_cancel1_94c871ed607b
-- name    : P2M_GroundTheory_Heights__Heights_LineChowForm_cancel1_94c871ed607b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:50.103068+00:00
-- url     : https://prove2.me/theorems/13d4893f-8910-46d5-9695-1ba4301efba0
-- title:
--   P2 M Ground Theory Heights  Heights Line Chow Form cancel1 94c871ed607b: P2 M Ground Theory Heights  Heights Line Chow Form cancel1 94c871ed607b
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Chow Form cancel1 94c871ed607b construction uses the P2 M Ground Theory Heights  Heights Line Chow Form cancel1 94c871ed607b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L78-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L78-L92

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

theorem P2M_GroundTheory_Heights__Heights_LineChowForm_cancel1_94c871ed607b (h q : MvPolynomial (Fin 2 × Fin 2) F) (e : X (0,0) * h = D2 * q) : D2 ∣ h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineChowForm».«cancel1» := P2M_GroundTheory_Heights__Heights_LineChowForm_cancel1_94c871ed607b
