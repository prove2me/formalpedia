-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_not_mem_bot_952292a2748a
-- name    : P2M_GroundTheory_Heights__Heights_linForm_single_not_mem_bot_952292a2748a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:50.218235+00:00
-- url     : https://prove2.me/theorems/3f22068f-83b1-4ae0-b54c-4d521cda0383
-- title:
--   P2 M Ground Theory Heights  Heights lin Form single not mem bot 952292a2748a: P2 M Ground Theory Heights  Heights lin Form single not mem bot 952292a2748a
-- statement:
--   The P2 M Ground Theory Heights  Heights lin Form single not mem bot 952292a2748a construction uses the P2 M Ground Theory Heights  Heights lin Form single not mem bot 952292a2748a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L252-L255

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_linForm_single_not_mem_bot_952292a2748a {n : ℕ} (i : Fin n) :
    linForm (Pi.single i (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linForm_single_not_mem_bot» := P2M_GroundTheory_Heights__Heights_linForm_single_not_mem_bot_952292a2748a
