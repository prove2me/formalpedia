-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
-- name    : P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:32.698074+00:00
-- url     : https://prove2.me/theorems/72499861-cc76-41e4-8b3b-747ee1d37397
-- title:
--   P2 M Ground Theory Heights  Heights cont Diff eucl Pot 53e03a97724f: P2 M Ground Theory Heights  Heights cont Diff eucl Pot 53e03a97724f
-- statement:
--   The P2 M Ground Theory Heights  Heights cont Diff eucl Pot 53e03a97724f construction uses the P2 M Ground Theory Heights  Heights cont Diff eucl Pot 53e03a97724f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L248-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L248-L250

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

theorem P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f (n : ℕ) : ContDiff ℝ ∞ (euclPot : (Fin n → ℂ) → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«contDiff_euclPot» := P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
