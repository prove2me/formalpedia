-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_analyticAt_eval_poly_5731e866b48a
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_analyticAt_eval_poly_5731e866b48a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:27.353379+00:00
-- url     : https://prove2.me/theorems/bf8bbb57-52f8-44d8-89ef-8f5387f59279
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One analytic At eval poly 5731e866b48a: P2 M Ground Theory Heights  Heights Tube Deep Rank One analytic At eval poly 5731e866b48a
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One analytic At eval poly 5731e866b48a construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One analytic At eval poly 5731e866b48a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L67-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepRankOne
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
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TubeDeepRankOne

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_analyticAt_eval_poly_5731e866b48a {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    AnalyticAt ℂ (fun z => eval z P) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«analyticAt_eval_poly» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_analyticAt_eval_poly_5731e866b48a
