-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_const_mul_dpow_df0a3ef03557
-- name    : P2M_GroundTheory_Heights__Heights_integral_const_mul_dpow_df0a3ef03557
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:09.023853+00:00
-- url     : https://prove2.me/theorems/f3715a79-35db-4a92-807e-1bdc6e516f7c
-- title:
--   P2 M Ground Theory Heights  Heights integral const mul dpow df0a3ef03557: P2 M Ground Theory Heights  Heights integral const mul dpow df0a3ef03557
-- statement:
--   The P2 M Ground Theory Heights  Heights integral const mul dpow df0a3ef03557 construction uses the P2 M Ground Theory Heights  Heights integral const mul dpow df0a3ef03557 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegRadialWeight.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegRadialWeight.lean#L19-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_integral_const_mul_dpow_df0a3ef03557 (e : ℕ) (c t : ℝ) :
    ∫ τ in (0 : ℝ)..t, c * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) = c * t ^ (e + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«integral_const_mul_dpow» := P2M_GroundTheory_Heights__Heights_integral_const_mul_dpow_df0a3ef03557
