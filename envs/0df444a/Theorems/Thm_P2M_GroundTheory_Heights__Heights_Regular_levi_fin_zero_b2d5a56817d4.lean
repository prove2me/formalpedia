-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_levi_fin_zero_b2d5a56817d4
-- name    : P2M_GroundTheory_Heights__Heights_Regular_levi_fin_zero_b2d5a56817d4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:33.414955+00:00
-- url     : https://prove2.me/theorems/ab860591-e6cf-48b0-95b4-d09f6d9d68fc
-- title:
--   P2 M Ground Theory Heights  Heights Regular levi fin zero b2d5a56817d4: P2 M Ground Theory Heights  Heights Regular levi fin zero b2d5a56817d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular levi fin zero b2d5a56817d4 construction uses the P2 M Ground Theory Heights  Heights Regular levi fin zero b2d5a56817d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L402-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L402-L405

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_levi_fin_zero_b2d5a56817d4 (φ : (Fin 0 → ℂ) → ℝ) (z w : Fin 0 → ℂ) : levi φ z w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«levi_fin_zero» := P2M_GroundTheory_Heights__Heights_Regular_levi_fin_zero_b2d5a56817d4
