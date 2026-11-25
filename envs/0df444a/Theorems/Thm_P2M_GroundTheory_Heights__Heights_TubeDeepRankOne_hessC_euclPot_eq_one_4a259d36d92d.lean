-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_eq_one_4a259d36d92d
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_eq_one_4a259d36d92d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:21.590923+00:00
-- url     : https://prove2.me/theorems/80dddbf9-88da-44c4-9c68-2672a19040a3
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C eucl Pot eq one 4a259d36d92d: P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C eucl Pot eq one 4a259d36d92d
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C eucl Pot eq one 4a259d36d92d construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One hess C eucl Pot eq one 4a259d36d92d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L51-L56

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

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_eq_one_4a259d36d92d {N : ℕ} (z : Fin N → ℂ) : hessC (euclPot : (Fin N → ℂ) → ℝ) z = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«hessC_euclPot_eq_one» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_eq_one_4a259d36d92d
