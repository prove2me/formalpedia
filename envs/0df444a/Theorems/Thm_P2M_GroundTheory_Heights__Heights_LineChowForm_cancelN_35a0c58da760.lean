-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_cancelN_35a0c58da760
-- name    : P2M_GroundTheory_Heights__Heights_LineChowForm_cancelN_35a0c58da760
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:43.471474+00:00
-- url     : https://prove2.me/theorems/89c0f265-4735-4dff-ab6f-9cf41a1779fd
-- title:
--   P2 M Ground Theory Heights  Heights Line Chow Form cancel N 35a0c58da760: P2 M Ground Theory Heights  Heights Line Chow Form cancel N 35a0c58da760
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Chow Form cancel N 35a0c58da760 construction uses the P2 M Ground Theory Heights  Heights Line Chow Form cancel N 35a0c58da760 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L94-L99

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

theorem P2M_GroundTheory_Heights__Heights_LineChowForm_cancelN_35a0c58da760 (N : ℕ) (g : MvPolynomial (Fin 2 × Fin 2) F) (h : D2 ∣ X (0,0) ^ N * g) : D2 ∣ g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineChowForm».«cancelN» := P2M_GroundTheory_Heights__Heights_LineChowForm_cancelN_35a0c58da760
