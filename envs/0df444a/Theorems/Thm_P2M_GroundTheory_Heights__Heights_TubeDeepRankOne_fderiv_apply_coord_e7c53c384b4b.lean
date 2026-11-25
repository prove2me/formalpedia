-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_fderiv_apply_coord_e7c53c384b4b
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_fderiv_apply_coord_e7c53c384b4b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:46:10.516289+00:00
-- url     : https://prove2.me/theorems/ff654f76-2267-5d7f-9306-6affd6c29521
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One fderiv apply coord e7c53c384b4b: P2 M Ground Theory Heights  Heights Tube Deep Rank One fderiv apply coord e7c53c384b4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One fderiv apply coord e7c53c384b4b construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One fderiv apply coord e7c53c384b4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L134-L141

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

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_fderiv_apply_coord_e7c53c384b4b {D m : ℕ} (F : (Fin D → ℂ) → Fin m → ℂ) (y h : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F y) (a : Fin m) :
    fderiv ℂ F y h a = fderiv ℂ (fun x => F x a) y h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«fderiv_apply_coord» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_fderiv_apply_coord_e7c53c384b4b
