-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ImplicitCurve_analyticOnNhd_of_differentiableOn_12cdb7d22a35
-- name    : P2M_GroundTheory_Heights__Heights_ImplicitCurve_analyticOnNhd_of_differentiableOn_12cdb7d22a35
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:27.937957+00:00
-- url     : https://prove2.me/theorems/07ba4280-a482-4534-9d70-a9ba2c1f3e79
-- title:
--   P2 M Ground Theory Heights  Heights Implicit Curve analytic On Nhd of differentiable On 12cdb7d22a35: P2 M Ground Theory Heights  Heights Implicit Curve analytic On Nhd of differentiable On 12cdb7d22a
-- statement:
--   The P2 M Ground Theory Heights  Heights Implicit Curve analytic On Nhd of differentiable On 12cdb7d22a35 construction uses the P2 M Ground Theory Heights  Heights Implicit Curve analytic On Nhd of differentiable On 12cdb7d22a35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PImplicitCurve.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PImplicitCurve.lean#L14-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StImplicitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PImplicitCurve
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
open Matrix Topology Metric
noncomputable section
open GroundTheory.Heights₂.Heights.ImplicitCurve

theorem P2M_GroundTheory_Heights__Heights_ImplicitCurve_analyticOnNhd_of_differentiableOn_12cdb7d22a35 {m p : ℕ} {U : Set (Fin m → ℂ)}
    {Φ : (Fin m → ℂ) → Fin p → ℂ} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) :
    AnalyticOnNhd ℂ Φ U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ImplicitCurve».«analyticOnNhd_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_ImplicitCurve_analyticOnNhd_of_differentiableOn_12cdb7d22a35
