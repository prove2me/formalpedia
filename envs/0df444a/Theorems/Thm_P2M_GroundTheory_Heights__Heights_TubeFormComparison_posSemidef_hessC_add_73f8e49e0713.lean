-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_add_73f8e49e0713
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_add_73f8e49e0713
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:51.119077+00:00
-- url     : https://prove2.me/theorems/268e7215-1ce9-4742-b075-2c85360814be
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison pos Semidef hess C add 73f8e49e0713: P2 M Ground Theory Heights  Heights Tube Form Comparison pos Semidef hess C add 73f8e49e0713
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison pos Semidef hess C add 73f8e49e0713 construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison pos Semidef hess C add 73f8e49e0713 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L66-L79

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

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_add_73f8e49e0713 {N : ℕ} {f : (Fin N → ℂ) → ℝ} {x : Fin N → ℂ} (hf : ContDiffAt ℝ 2 f x)
    {c : ℝ} (hc : 0 ≤ c) (hl : ∀ w, -c * ‖w‖ ^ 2 ≤ levi f x w) :
    (hessC f x + (c : ℂ) • 1).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«posSemidef_hessC_add» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_add_73f8e49e0713
