-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_comp_54803d612c25
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_comp_54803d612c25
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:50.725539+00:00
-- url     : https://prove2.me/theorems/c693e601-5ef3-4b20-8d8d-aaae66bec6e7
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C eucl Pot comp 54803d612c25: P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C eucl Pot comp 54803d612c25
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C eucl Pot comp 54803d612c25 construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C eucl Pot comp 54803d612c25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L58-L65

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

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_comp_54803d612c25 {n D : ℕ} (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ)
    (hs : AnalyticAt ℂ s y) :
    hessC (euclPot ∘ s) y = ∑ m, vecMulVec (fun j => jacC s y m j) (star fun j => jacC s y m j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«hessC_euclPot_comp» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_comp_54803d612c25
