-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isFiniteProjection_space_4c67b3bfb6bf
-- name    : P2M_GroundTheory_Heights__Heights_isFiniteProjection_space_4c67b3bfb6bf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:19.214801+00:00
-- url     : https://prove2.me/theorems/e7dac0aa-de0f-4bde-af03-9d1821c39047
-- title:
--   P2 M Ground Theory Heights  Heights is Finite Projection space 4c67b3bfb6bf: P2 M Ground Theory Heights  Heights is Finite Projection space 4c67b3bfb6bf
-- statement:
--   The P2 M Ground Theory Heights  Heights is Finite Projection space 4c67b3bfb6bf construction uses the P2 M Ground Theory Heights  Heights is Finite Projection space 4c67b3bfb6bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L183-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L183-L191

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

theorem P2M_GroundTheory_Heights__Heights_isFiniteProjection_space_4c67b3bfb6bf (n : ℕ) :
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isFiniteProjection_space» := P2M_GroundTheory_Heights__Heights_isFiniteProjection_space_4c67b3bfb6bf
