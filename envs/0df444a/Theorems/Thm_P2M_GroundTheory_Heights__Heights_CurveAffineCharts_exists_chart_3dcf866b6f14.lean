-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:50.167081+00:00
-- url     : https://prove2.me/theorems/ab128675-7854-4591-8f00-b6cf7efd199e
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts exists chart 3dcf866b6f14: P2 M Ground Theory Heights  Heights Curve Affine Charts exists chart 3dcf866b6f14
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts exists chart 3dcf866b6f14 construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts exists chart 3dcf866b6f14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L16-L19

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

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14 (hy : IsArithVar (mCoordIdeal y) 1) : ∃ t : T, y ⟨(), t⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«exists_chart» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14
