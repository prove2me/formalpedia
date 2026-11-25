-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_euclPot_ff6b1ef3877d
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_euclPot_ff6b1ef3877d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:41.11475+00:00
-- url     : https://prove2.me/theorems/92aad9f8-9fb3-4d7e-a6a1-bd96256c72c6
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison levi eucl Pot ff6b1ef3877d: P2 M Ground Theory Heights  Heights Tube Form Comparison levi eucl Pot ff6b1ef3877d
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison levi eucl Pot ff6b1ef3877d construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison levi eucl Pot ff6b1ef3877d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L38-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_euclPot_ff6b1ef3877d {N : ℕ} (z w : Fin N → ℂ) : levi euclPot z w = ∑ j, ‖w j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«levi_euclPot» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_euclPot_ff6b1ef3877d
