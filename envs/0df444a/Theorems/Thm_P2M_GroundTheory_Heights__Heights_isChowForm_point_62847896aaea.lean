-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
-- name    : P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:04.199172+00:00
-- url     : https://prove2.me/theorems/26edf50f-f0f0-48ae-bcbb-b2461fac4aad
-- title:
--   P2 M Ground Theory Heights  Heights is Chow Form point 62847896aaea: P2 M Ground Theory Heights  Heights is Chow Form point 62847896aaea
-- statement:
--   The P2 M Ground Theory Heights  Heights is Chow Form point 62847896aaea construction uses the P2 M Ground Theory Heights  Heights is Chow Form point 62847896aaea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L318-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L318-L323

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
open MvPolynomial MeasureTheory NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea (F : Type*) [Field F] :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 (X (0, 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isChowForm_point» := P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
