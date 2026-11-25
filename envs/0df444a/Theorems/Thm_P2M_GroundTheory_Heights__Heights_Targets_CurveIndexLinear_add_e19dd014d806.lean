-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinear_add_e19dd014d806
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinear_add_e19dd014d806
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:13.758085+00:00
-- url     : https://prove2.me/theorems/1e66643c-3844-419c-b58f-096ce126c273
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear add e19dd014d806: P2 M Ground Theory Heights  Heights Targets Curve Index Linear add e19dd014d806
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear add e19dd014d806 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear add e19dd014d806 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L259-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L259-L279

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
open CurveIndexLinearAlt

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinear_add_e19dd014d806 (hF : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement)
    (hI : InvertibleIndexMul.Statement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hP : IsArithVar (mCoordIdeal y) 1)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a a' : K → ℤ) :
    chartIndexLog y c (a + a') 1 = chartIndexLog y c a 1 + chartIndexLog y c a' 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinear».«add» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinear_add_e19dd014d806
