-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_radialTransform_eq_zero_of_const_e9745533580f
-- name    : P2M_GroundTheory_Heights__Heights_radialTransform_eq_zero_of_const_e9745533580f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:15.935618+00:00
-- url     : https://prove2.me/theorems/50ad4edd-8a7f-47dd-b098-121f8fad3e1a
-- title:
--   P2 M Ground Theory Heights  Heights radial Transform eq zero of const e9745533580f: P2 M Ground Theory Heights  Heights radial Transform eq zero of const e9745533580f
-- statement:
--   The P2 M Ground Theory Heights  Heights radial Transform eq zero of const e9745533580f construction uses the P2 M Ground Theory Heights  Heights radial Transform eq zero of const e9745533580f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegRadialWeight.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegRadialWeight.lean#L27-L36

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

theorem P2M_GroundTheory_Heights__Heights_radialTransform_eq_zero_of_const_e9745533580f (e : ℕ) (a : ℝ → ℝ) {t₀ t : ℝ}
    (ha : ∀ τ ∈ Set.Icc 0 t₀, a τ = a 0) (ht : t ∈ Set.Icc 0 t₀) :
    radialTransform (e + 1) a t = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«radialTransform_eq_zero_of_const» := P2M_GroundTheory_Heights__Heights_radialTransform_eq_zero_of_const_e9745533580f
