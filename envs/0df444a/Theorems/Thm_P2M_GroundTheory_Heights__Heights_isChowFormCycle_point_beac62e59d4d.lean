-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowFormCycle_point_beac62e59d4d
-- name    : P2M_GroundTheory_Heights__Heights_isChowFormCycle_point_beac62e59d4d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:54.430807+00:00
-- url     : https://prove2.me/theorems/c4748d20-12ca-4408-8729-37f587cf8b20
-- title:
--   P2 M Ground Theory Heights  Heights is Chow Form Cycle point beac62e59d4d: P2 M Ground Theory Heights  Heights is Chow Form Cycle point beac62e59d4d
-- statement:
--   The P2 M Ground Theory Heights  Heights is Chow Form Cycle point beac62e59d4d construction uses the P2 M Ground Theory Heights  Heights is Chow Form Cycle point beac62e59d4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L340-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L340-L347

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

theorem P2M_GroundTheory_Heights__Heights_isChowFormCycle_point_beac62e59d4d (F : Type*) [Field F] :
    IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1) 1 (X (0, 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isChowFormCycle_point» := P2M_GroundTheory_Heights__Heights_isChowFormCycle_point_beac62e59d4d
