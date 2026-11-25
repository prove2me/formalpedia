-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_pointCutoff_d7eee880fa4e
-- name    : P2M_GroundTheory_Heights__Heights_Regular_pointCutoff_d7eee880fa4e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:14.718889+00:00
-- url     : https://prove2.me/theorems/da87ee84-bc19-45ed-baa8-a7efc98100c9
-- title:
--   P2 M Ground Theory Heights  Heights Regular point Cutoff d7eee880fa4e: P2 M Ground Theory Heights  Heights Regular point Cutoff d7eee880fa4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular point Cutoff d7eee880fa4e construction uses the P2 M Ground Theory Heights  Heights Regular point Cutoff d7eee880fa4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L407-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L407-L412

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

theorem P2M_GroundTheory_Heights__Heights_Regular_pointCutoff_d7eee880fa4e : pointCharts.IsCutoffFamily (fun _ _ => 0) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«pointCutoff» := P2M_GroundTheory_Heights__Heights_Regular_pointCutoff_d7eee880fa4e
