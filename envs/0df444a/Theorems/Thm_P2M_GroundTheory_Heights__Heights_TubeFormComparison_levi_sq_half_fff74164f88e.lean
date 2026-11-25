-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_sq_half_fff74164f88e
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_sq_half_fff74164f88e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:17.846839+00:00
-- url     : https://prove2.me/theorems/c967bf12-eda3-5bb7-8d81-75dbe0316e8a
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison levi sq half fff74164f88e: P2 M Ground Theory Heights  Heights Tube Form Comparison levi sq half fff74164f88e
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison levi sq half fff74164f88e construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison levi sq half fff74164f88e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L121-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L121-L143

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

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_sq_half_fff74164f88e {N : ℕ} {v : (Fin N → ℂ) → ℝ} {y : Fin N → ℂ} (hv : ContDiffAt ℝ 2 v y)
    (w : Fin N → ℂ) :
    levi (fun z => v z ^ 2 / 2) y w =
      ((fderiv ℝ v y w) ^ 2 + (fderiv ℝ v y (Complex.I • w)) ^ 2) / 4 + v y * levi v y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«levi_sq_half» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_sq_half_fff74164f88e
