-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finite_1e9464aa5696
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finite_1e9464aa5696
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:24.185874+00:00
-- url     : https://prove2.me/theorems/6da7916c-91fb-4bd6-9469-2faaf77fbc77
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts finite 1e9464aa5696: P2 M Ground Theory Heights  Heights Curve Affine Charts finite 1e9464aa5696
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts finite 1e9464aa5696 construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts finite 1e9464aa5696 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L55-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finite_1e9464aa5696 [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) : Module.Finite ℤ (curveRing y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«finite» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finite_1e9464aa5696
