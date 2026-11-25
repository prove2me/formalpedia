-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartRingZ_le_loc_4f0655af7099
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartRingZ_le_loc_4f0655af7099
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:24.500527+00:00
-- url     : https://prove2.me/theorems/6327c067-256f-4c4e-8bd8-bb9702cf9b78
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt chart Ring Z le loc 4f0655af7099: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt chart Ring Z le loc 4f0655af7099
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt chart Ring Z le loc 4f0655af7099 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt chart Ring Z le loc 4f0655af7099 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L150-L158

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartRingZ_le_loc_4f0655af7099 {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} (hm : m.IsPrime) {c' : ∀ k, ι k}
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c' p.1⟩) = α) {r : Ω}
    (hrc : r ∈ chartRingZ y c') : ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * r ∈ curveRing y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«chartRingZ_le_loc» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartRingZ_le_loc_4f0655af7099
