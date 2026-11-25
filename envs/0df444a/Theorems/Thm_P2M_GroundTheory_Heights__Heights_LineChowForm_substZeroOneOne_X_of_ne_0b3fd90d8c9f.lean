-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_substZeroOneOne_X_of_ne_0b3fd90d8c9f
-- name    : P2M_GroundTheory_Heights__Heights_LineChowForm_substZeroOneOne_X_of_ne_0b3fd90d8c9f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:01.397583+00:00
-- url     : https://prove2.me/theorems/76cd1582-5f2c-48fd-9168-7f50f02c56c9
-- title:
--   P2 M Ground Theory Heights  Heights Line Chow Form subst Zero One One X of ne 0b3fd90d8c9f: P2 M Ground Theory Heights  Heights Line Chow Form subst Zero One One X of ne 0b3fd90d8c9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Chow Form subst Zero One One X of ne 0b3fd90d8c9f construction uses the P2 M Ground Theory Heights  Heights Line Chow Form subst Zero One One X of ne 0b3fd90d8c9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L48-L50

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

theorem P2M_GroundTheory_Heights__Heights_LineChowForm_substZeroOneOne_X_of_ne_0b3fd90d8c9f (i : Fin 2 × Fin 2) (hi : i ≠ (1,1)) :
    substZeroOneOne (X i : MvPolynomial (Fin 2 × Fin 2) F) = X i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineChowForm».«substZeroOneOne_X_of_ne» := P2M_GroundTheory_Heights__Heights_LineChowForm_substZeroOneOne_X_of_ne_0b3fd90d8c9f
