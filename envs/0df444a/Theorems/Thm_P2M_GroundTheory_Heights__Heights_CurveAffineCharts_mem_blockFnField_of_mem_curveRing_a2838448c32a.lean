-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_blockFnField_of_mem_curveRing_a2838448c32a
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_blockFnField_of_mem_curveRing_a2838448c32a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:55.368829+00:00
-- url     : https://prove2.me/theorems/aca18bae-197c-5f96-b188-0ef50fea3249
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts mem block Fn Field of mem curve Ring a2838448c32a: P2 M Ground Theory Heights  Heights Curve Affine Charts mem block Fn Field of mem curve Ring
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts mem block Fn Field of mem curve Ring a2838448c32a construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts mem block Fn Field of mem curve Ring a2838448c32a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L63-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L63-L74

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

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_blockFnField_of_mem_curveRing_a2838448c32a [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ blockFnField y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«mem_blockFnField_of_mem_curveRing» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_blockFnField_of_mem_curveRing_a2838448c32a
