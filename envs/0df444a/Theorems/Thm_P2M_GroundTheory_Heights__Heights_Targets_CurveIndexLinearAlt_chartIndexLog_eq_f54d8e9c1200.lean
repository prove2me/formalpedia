-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartIndexLog_eq_f54d8e9c1200
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartIndexLog_eq_f54d8e9c1200
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:09.675038+00:00
-- url     : https://prove2.me/theorems/abcee9a5-b67d-44aa-8545-921dfd629440
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt chart Index Log eq f54d8e9c1200: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt chart Index Log eq f54d8e9c1200
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt chart Index Log eq f54d8e9c1200 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt chart Index Log eq f54d8e9c1200 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L103-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L103-L116

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartIndexLog_eq_f54d8e9c1200 {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) :
    chartIndexLog y c a 1 = Real.log (genIndex (secIdeal y c a) (curveRing y).toAddSubgroup) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«chartIndexLog_eq» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartIndexLog_eq_f54d8e9c1200
