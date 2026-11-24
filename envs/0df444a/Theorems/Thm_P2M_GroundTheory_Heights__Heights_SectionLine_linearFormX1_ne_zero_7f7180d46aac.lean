-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionLine_linearFormX1_ne_zero_7f7180d46aac
-- name    : P2M_GroundTheory_Heights__Heights_SectionLine_linearFormX1_ne_zero_7f7180d46aac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:51.674932+00:00
-- url     : https://prove2.me/theorems/2d611c21-34b4-4ed2-aab1-c3518c865c4e
-- title:
--   P2 M Ground Theory Heights  Heights Section Line linear Form X1 ne zero 7f7180d46aac: P2 M Ground Theory Heights  Heights Section Line linear Form X1 ne zero 7f7180d46aac
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Line linear Form X1 ne zero 7f7180d46aac construction uses the P2 M Ground Theory Heights  Heights Section Line linear Form X1 ne zero 7f7180d46aac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SectionLineAnyField.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SectionLineAnyField.lean#L24-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SectionLineAnyField
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
open MvPolynomial LineChowForm
noncomputable section
open GroundTheory.Heights₂.Heights.SectionLine
variable (F : Type) [Field F]

theorem P2M_GroundTheory_Heights__Heights_SectionLine_linearFormX1_ne_zero_7f7180d46aac : linForm (coeffX1 F) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) F)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionLine».«linearFormX1_ne_zero» := P2M_GroundTheory_Heights__Heights_SectionLine_linearFormX1_ne_zero_7f7180d46aac
