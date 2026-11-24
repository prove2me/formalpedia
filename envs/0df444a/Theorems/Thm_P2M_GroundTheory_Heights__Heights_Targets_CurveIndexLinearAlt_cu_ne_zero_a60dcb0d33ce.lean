-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_ne_zero_a60dcb0d33ce
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_ne_zero_a60dcb0d33ce
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:59.345395+00:00
-- url     : https://prove2.me/theorems/14dd60d7-515c-4538-b98b-a67f94dd7c1a
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu ne zero a60dcb0d33ce: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu ne zero a60dcb0d33ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu ne zero a60dcb0d33ce construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu ne zero a60dcb0d33ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L26-L28

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_ne_zero_a60dcb0d33ce {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) :
    cu y c a ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«cu_ne_zero» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_ne_zero_a60dcb0d33ce
