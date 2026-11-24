-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_eq_re_bde4222f82b2
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_eq_re_bde4222f82b2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:32.723802+00:00
-- url     : https://prove2.me/theorems/160ac769-7bcb-43d5-a008-72ee7843005c
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison levi eq re bde4222f82b2: P2 M Ground Theory Heights  Heights Tube Form Comparison levi eq re bde4222f82b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison levi eq re bde4222f82b2 construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison levi eq re bde4222f82b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L20-L29

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

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_eq_re_bde4222f82b2 {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z a : Fin N → ℂ) :
    levi φ z a = (a ⬝ᵥ (hessC φ z *ᵥ star a)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«levi_eq_re» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_eq_re_bde4222f82b2
