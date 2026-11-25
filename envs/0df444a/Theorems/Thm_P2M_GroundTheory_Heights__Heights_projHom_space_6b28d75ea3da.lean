-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_projHom_space_6b28d75ea3da
-- name    : P2M_GroundTheory_Heights__Heights_projHom_space_6b28d75ea3da
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:35.942629+00:00
-- url     : https://prove2.me/theorems/a877a52e-5630-4ea6-8152-c07d71dd982e
-- title:
--   P2 M Ground Theory Heights  Heights proj Hom space 6b28d75ea3da: P2 M Ground Theory Heights  Heights proj Hom space 6b28d75ea3da
-- statement:
--   The P2 M Ground Theory Heights  Heights proj Hom space 6b28d75ea3da construction uses the P2 M Ground Theory Heights  Heights proj Hom space 6b28d75ea3da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L175-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L175-L181

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

theorem P2M_GroundTheory_Heights__Heights_projHom_space_6b28d75ea3da (n : ℕ) :
    projHom (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) =
      Ideal.Quotient.mkₐ ℂ ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«projHom_space» := P2M_GroundTheory_Heights__Heights_projHom_space_6b28d75ea3da
