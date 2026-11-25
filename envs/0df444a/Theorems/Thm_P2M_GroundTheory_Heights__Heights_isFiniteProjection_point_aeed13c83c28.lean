-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isFiniteProjection_point_aeed13c83c28
-- name    : P2M_GroundTheory_Heights__Heights_isFiniteProjection_point_aeed13c83c28
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:16.498799+00:00
-- url     : https://prove2.me/theorems/b9e337e6-f776-50d4-8bcb-580e480bce8c
-- title:
--   P2 M Ground Theory Heights  Heights is Finite Projection point aeed13c83c28: P2 M Ground Theory Heights  Heights is Finite Projection point aeed13c83c28
-- statement:
--   The P2 M Ground Theory Heights  Heights is Finite Projection point aeed13c83c28 construction uses the P2 M Ground Theory Heights  Heights is Finite Projection point aeed13c83c28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L216-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L216-L236

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

theorem P2M_GroundTheory_Heights__Heights_isFiniteProjection_point_aeed13c83c28 {n : ℕ} (p : Fin n → ℂ) (A : Matrix (Fin 0) (Fin n) ℂ) :
    IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isFiniteProjection_point» := P2M_GroundTheory_Heights__Heights_isFiniteProjection_point_aeed13c83c28
