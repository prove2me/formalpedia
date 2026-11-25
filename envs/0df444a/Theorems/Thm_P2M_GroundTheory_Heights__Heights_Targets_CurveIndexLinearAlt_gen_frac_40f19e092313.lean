-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_frac_40f19e092313
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_frac_40f19e092313
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:59.33085+00:00
-- url     : https://prove2.me/theorems/3490e437-6d3d-4af8-b333-7b16fd8b81be
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt gen frac 40f19e092313: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt gen frac 40f19e092313
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt gen frac 40f19e092313 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt gen frac 40f19e092313 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L221-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L221-L253

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_frac_40f19e092313 {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {m : Ideal (curveRing y)}
    {c0 : ∀ k, ι k} (hc0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0)
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c0 p.1⟩) = α)
    (c' : ∀ k, ι k) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a : K → ℤ) :
    ∃ d ∈ curveRing y, d ≠ 0 ∧ d * gen y c a c' ∈ curveRing y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«gen_frac» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_frac_40f19e092313
