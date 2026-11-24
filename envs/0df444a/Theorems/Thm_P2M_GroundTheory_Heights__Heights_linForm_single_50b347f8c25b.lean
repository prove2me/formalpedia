-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b
-- name    : P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:26.9281+00:00
-- url     : https://prove2.me/theorems/84c37665-503d-4b74-941f-2de2bac07033
-- title:
--   P2 M Ground Theory Heights  Heights lin Form single 50b347f8c25b: P2 M Ground Theory Heights  Heights lin Form single 50b347f8c25b
-- statement:
--   The P2 M Ground Theory Heights  Heights lin Form single 50b347f8c25b construction uses the P2 M Ground Theory Heights  Heights lin Form single 50b347f8c25b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L171-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L171-L173

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

theorem P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : ℂ)) = X i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linForm_single» := P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b
