-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isPsh_normSq_ball_f0c3bcbba220
-- name    : P2M_GroundTheory_Heights__Heights_Regular_isPsh_normSq_ball_f0c3bcbba220
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:27.107302+00:00
-- url     : https://prove2.me/theorems/f26666c2-130b-4b4a-94d6-a6477d6b82dd
-- title:
--   P2 M Ground Theory Heights  Heights Regular is Psh norm Sq ball f0c3bcbba220: P2 M Ground Theory Heights  Heights Regular is Psh norm Sq ball f0c3bcbba220
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular is Psh norm Sq ball f0c3bcbba220 construction uses the P2 M Ground Theory Heights  Heights Regular is Psh norm Sq ball f0c3bcbba220 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L305-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L305-L307

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

theorem P2M_GroundTheory_Heights__Heights_Regular_isPsh_normSq_ball_f0c3bcbba220 (D : ℕ) :
    IsPsh (ball (0 : Fin D → ℂ) 2) (fun z => ∑ j, ‖z j‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«isPsh_normSq_ball» := P2M_GroundTheory_Heights__Heights_Regular_isPsh_normSq_ball_f0c3bcbba220
