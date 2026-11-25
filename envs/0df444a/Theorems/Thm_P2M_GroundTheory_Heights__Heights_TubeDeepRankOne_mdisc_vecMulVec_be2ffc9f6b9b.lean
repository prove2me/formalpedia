-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_vecMulVec_be2ffc9f6b9b
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_vecMulVec_be2ffc9f6b9b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:07.970677+00:00
-- url     : https://prove2.me/theorems/116f56dd-198f-4bf2-8df2-b74b78d5bb7c
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One mdisc vec Mul Vec be2ffc9f6b9b: P2 M Ground Theory Heights  Heights Tube Deep Rank One mdisc vec Mul Vec be2ffc9f6b9b
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One mdisc vec Mul Vec be2ffc9f6b9b construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One mdisc vec Mul Vec be2ffc9f6b9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L18-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L18-L39

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

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_vecMulVec_be2ffc9f6b9b {D : ℕ} (u : Fin D → Fin D → ℂ) :
    mdisc (fun k => vecMulVec (u k) (star (u k))) =
      (1 / (D.factorial : ℂ)) * (Complex.normSq (Matrix.of u).det : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«mdisc_vecMulVec» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_vecMulVec_be2ffc9f6b9b
