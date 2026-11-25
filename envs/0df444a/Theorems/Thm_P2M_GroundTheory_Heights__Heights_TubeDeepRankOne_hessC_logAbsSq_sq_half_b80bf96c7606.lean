-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_logAbsSq_sq_half_b80bf96c7606
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_logAbsSq_sq_half_b80bf96c7606
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:02.351506+00:00
-- url     : https://prove2.me/theorems/babd17f5-2ecb-4862-be98-8ef24d5c3585
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C log Abs Sq sq half b80bf96c7606: P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C log Abs Sq sq half b80bf96c7606
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C log Abs Sq sq half b80bf96c7606 construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C log Abs Sq sq half b80bf96c7606 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L113-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L113-L132

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

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_logAbsSq_sq_half_b80bf96c7606 {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0) :
    hessC (fun z => logAbsSq P z ^ 2 / 2) y =
      vecMulVec (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (star fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«hessC_logAbsSq_sq_half» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_logAbsSq_sq_half_b80bf96c7606
