-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integralClosure_of_mem_curveRing_b6c172556c3d
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integralClosure_of_mem_curveRing_b6c172556c3d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:36:06.820358+00:00
-- url     : https://prove2.me/theorems/dba0a371-dc0b-4399-902a-b069a647a3ff
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts mem integral Closure of mem curve Ring b6c172556c3d: P2 M Ground Theory Heights  Heights Curve Affine Charts mem integral Closure of mem curve R
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts mem integral Closure of mem curve Ring b6c172556c3d construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts mem integral Closure of mem curve Ring b6c172556c3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L37-L53

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

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integralClosure_of_mem_curveRing_b6c172556c3d [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ integralClosure ℤ K' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«mem_integralClosure_of_mem_curveRing» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integralClosure_of_mem_curveRing_b6c172556c3d
