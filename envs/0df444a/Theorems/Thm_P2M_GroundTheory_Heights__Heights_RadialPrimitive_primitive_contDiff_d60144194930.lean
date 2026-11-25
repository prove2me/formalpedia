-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RadialPrimitive_primitive_contDiff_d60144194930
-- name    : P2M_GroundTheory_Heights__Heights_RadialPrimitive_primitive_contDiff_d60144194930
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:23.441434+00:00
-- url     : https://prove2.me/theorems/2e498b14-8dbd-4637-aa1a-49b1a01ec6f7
-- title:
--   P2 M Ground Theory Heights  Heights Radial Primitive primitive cont Diff d60144194930: P2 M Ground Theory Heights  Heights Radial Primitive primitive cont Diff d60144194930
-- statement:
--   The P2 M Ground Theory Heights  Heights Radial Primitive primitive cont Diff d60144194930 construction uses the P2 M Ground Theory Heights  Heights Radial Primitive primitive cont Diff d60144194930 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRadialPrimitive.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRadialPrimitive.lean#L12-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRadialPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRadialPrimitive
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
open MeasureTheory
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RadialPrimitive_primitive_contDiff_d60144194930 (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => ∫ τ in c..t, f τ) ∧ deriv (fun t => ∫ τ in c..t, f τ) = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RadialPrimitive».«primitive_contDiff» := P2M_GroundTheory_Heights__Heights_RadialPrimitive_primitive_contDiff_d60144194930
