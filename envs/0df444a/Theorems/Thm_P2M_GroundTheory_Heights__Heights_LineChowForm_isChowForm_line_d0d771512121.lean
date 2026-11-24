-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121
-- name    : P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:38.054562+00:00
-- url     : https://prove2.me/theorems/7942f9de-4f64-46b4-8d6f-460953217ef9
-- title:
--   P2 M Ground Theory Heights  Heights Line Chow Form is Chow Form line d0d771512121: P2 M Ground Theory Heights  Heights Line Chow Form is Chow Form line d0d771512121
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Chow Form is Chow Form line d0d771512121 construction uses the P2 M Ground Theory Heights  Heights Line Chow Form is Chow Form line d0d771512121 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L118-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L118-L177

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

theorem P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121 :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) F)) 2 (D2 : MvPolynomial (Fin 2 × Fin 2) F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineChowForm».«isChowForm_line» := P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121
