-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_euclPot_8b94f23095e1
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_euclPot_8b94f23095e1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:40.704147+00:00
-- url     : https://prove2.me/theorems/e0a0347b-c58b-488b-9fde-610f04033595
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison hess C eucl Pot 8b94f23095e1: P2 M Ground Theory Heights  Heights Tube Form Comparison hess C eucl Pot 8b94f23095e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison hess C eucl Pot 8b94f23095e1 construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison hess C eucl Pot 8b94f23095e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L31-L36

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

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_euclPot_8b94f23095e1 {N : ℕ} (z : Fin N → ℂ) : hessC (euclPot : (Fin N → ℂ) → ℝ) z = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«hessC_euclPot» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_euclPot_8b94f23095e1
