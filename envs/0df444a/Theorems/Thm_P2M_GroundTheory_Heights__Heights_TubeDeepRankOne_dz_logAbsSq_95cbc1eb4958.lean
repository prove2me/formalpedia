-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_dz_logAbsSq_95cbc1eb4958
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_dz_logAbsSq_95cbc1eb4958
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:12.069019+00:00
-- url     : https://prove2.me/theorems/cf9dc99c-1f1a-495f-a403-0d94860fa421
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One dz log Abs Sq 95cbc1eb4958: P2 M Ground Theory Heights  Heights Tube Deep Rank One dz log Abs Sq 95cbc1eb4958
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One dz log Abs Sq 95cbc1eb4958 construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One dz log Abs Sq 95cbc1eb4958 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L73-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L73-L111

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

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_dz_logAbsSq_95cbc1eb4958 {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0)
    (j : Fin m) :
    dz j (cplx (logAbsSq P)) y = fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«dz_logAbsSq» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_dz_logAbsSq_95cbc1eb4958
