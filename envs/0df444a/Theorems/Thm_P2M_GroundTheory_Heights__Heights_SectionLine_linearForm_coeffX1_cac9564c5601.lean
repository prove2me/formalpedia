-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionLine_linearForm_coeffX1_cac9564c5601
-- name    : P2M_GroundTheory_Heights__Heights_SectionLine_linearForm_coeffX1_cac9564c5601
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:56.977677+00:00
-- url     : https://prove2.me/theorems/4893778e-30df-405e-9a21-ee7f6cd3df07
-- title:
--   P2 M Ground Theory Heights  Heights Section Line linear Form coeff X1 cac9564c5601: P2 M Ground Theory Heights  Heights Section Line linear Form coeff X1 cac9564c5601
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Line linear Form coeff X1 cac9564c5601 construction uses the P2 M Ground Theory Heights  Heights Section Line linear Form coeff X1 cac9564c5601 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SectionLineAnyField.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SectionLineAnyField.lean#L21-L22

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

theorem P2M_GroundTheory_Heights__Heights_SectionLine_linearForm_coeffX1_cac9564c5601 : linForm (coeffX1 F) = (X 1 : MvPolynomial (Fin 2) F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionLine».«linearForm_coeffX1» := P2M_GroundTheory_Heights__Heights_SectionLine_linearForm_coeffX1_cac9564c5601
