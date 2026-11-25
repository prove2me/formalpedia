-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_uniform_denom_9c3df70fe533
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_uniform_denom_9c3df70fe533
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:50.425378+00:00
-- url     : https://prove2.me/theorems/b8f9fe5d-afc1-4799-bc1e-a51c63996660
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt uniform denom 9c3df70fe533: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt uniform denom 9c3df70fe533
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt uniform denom 9c3df70fe533 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt uniform denom 9c3df70fe533 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L160-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L160-L181

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_uniform_denom_9c3df70fe533 {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} (hm : m.IsPrime) (r : (∀ k, ι k) → Ω)
    (h : ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) →
      ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * r c'' ∈ chartRingZ y c'') :
    ∃ b : curveRing y, b ∉ m ∧ ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) →
      (b : Ω) * r c'' ∈ chartRingZ y c'' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«uniform_denom» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_uniform_denom_9c3df70fe533
