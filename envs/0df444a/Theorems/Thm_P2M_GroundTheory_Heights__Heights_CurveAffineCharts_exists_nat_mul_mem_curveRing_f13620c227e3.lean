-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_curveRing_f13620c227e3
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_curveRing_f13620c227e3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:10.472707+00:00
-- url     : https://prove2.me/theorems/c263e58c-8cc8-433a-86ef-c4841fdb1e2b
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts exists nat mul mem curve Ring f13620c227e3: P2 M Ground Theory Heights  Heights Curve Affine Charts exists nat mul mem curve Ring f13620c227e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts exists nat mul mem curve Ring f13620c227e3 construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts exists nat mul mem curve Ring f13620c227e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L125-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L125-L146

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

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_curveRing_f13620c227e3 [NumberField K'] {x : K'} (hx : x ∈ blockFnField y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ curveRing y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«exists_nat_mul_mem_curveRing» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_curveRing_f13620c227e3
