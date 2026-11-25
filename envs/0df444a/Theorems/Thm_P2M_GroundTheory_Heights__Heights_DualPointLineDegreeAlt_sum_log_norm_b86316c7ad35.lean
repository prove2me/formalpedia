-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_sum_log_norm_b86316c7ad35
-- name    : P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_sum_log_norm_b86316c7ad35
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:23.548674+00:00
-- url     : https://prove2.me/theorems/61fde9be-3a3b-4c91-8215-7b13ad9c00f9
-- title:
--   P2 M Ground Theory Heights  Heights Dual Point Line Degree Alt sum log norm b86316c7ad35: P2 M Ground Theory Heights  Heights Dual Point Line Degree Alt sum log norm b86316c7ad35
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Point Line Degree Alt sum log norm b86316c7ad35 construction uses the P2 M Ground Theory Heights  Heights Dual Point Line Degree Alt sum log norm b86316c7ad35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPointLineDegree.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPointLineDegree.lean#L17-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPointLineDegree
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualPointLineDegreeAlt

theorem P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_sum_log_norm_b86316c7ad35 {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointLineDegreeAlt».«sum_log_norm» := P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_sum_log_norm_b86316c7ad35
