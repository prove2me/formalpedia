-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_smooth_bump_81879bbf68ab
-- name    : P2M_GroundTheory_Heights__Heights_exists_smooth_bump_81879bbf68ab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:38.984794+00:00
-- url     : https://prove2.me/theorems/601166d1-ac04-439e-baf7-548a4e2be129
-- title:
--   P2 M Ground Theory Heights  Heights exists smooth bump 81879bbf68ab: P2 M Ground Theory Heights  Heights exists smooth bump 81879bbf68ab
-- statement:
--   The P2 M Ground Theory Heights  Heights exists smooth bump 81879bbf68ab construction uses the P2 M Ground Theory Heights  Heights exists smooth bump 81879bbf68ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L238-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L238-L242

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

theorem P2M_GroundTheory_Heights__Heights_exists_smooth_bump_81879bbf68ab (n : ℕ) :
    ∃ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f 0 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_smooth_bump» := P2M_GroundTheory_Heights__Heights_exists_smooth_bump_81879bbf68ab
