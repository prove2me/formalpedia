-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_add_fc4f2d1db5eb
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_add_fc4f2d1db5eb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:26.184428+00:00
-- url     : https://prove2.me/theorems/a373896c-3314-5255-867a-45b04631b4e1
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt gen add fc4f2d1db5eb: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt gen add fc4f2d1db5eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt gen add fc4f2d1db5eb construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt gen add fc4f2d1db5eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L66-L68

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_add_fc4f2d1db5eb {y : (Σ k, ι k) → Ω} {c c' : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a a' : K → ℤ) : gen y c (a + a') c' = gen y c a c' * gen y c a' c' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«gen_add» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_add_fc4f2d1db5eb
