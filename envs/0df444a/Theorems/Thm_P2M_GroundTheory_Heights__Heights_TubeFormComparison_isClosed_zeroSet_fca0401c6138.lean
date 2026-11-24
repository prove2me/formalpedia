-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_isClosed_zeroSet_fca0401c6138
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_isClosed_zeroSet_fca0401c6138
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:17.224793+00:00
-- url     : https://prove2.me/theorems/4057585d-b1cf-4b1b-adac-df40a482a45e
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison is Closed zero Set fca0401c6138: P2 M Ground Theory Heights  Heights Tube Form Comparison is Closed zero Set fca0401c6138
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison is Closed zero Set fca0401c6138 construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison is Closed zero Set fca0401c6138 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L248-L253

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

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_isClosed_zeroSet_fca0401c6138 {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«isClosed_zeroSet» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_isClosed_zeroSet_fca0401c6138
