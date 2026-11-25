-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_adjoin_e048a425d326
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_adjoin_e048a425d326
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:47.976735+00:00
-- url     : https://prove2.me/theorems/f588fb4a-2bdd-4f28-8dfe-730ef611e2f2
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts exists nat mul mem adjoin e048a425d326: P2 M Ground Theory Heights  Heights Curve Affine Charts exists nat mul mem adjoin e048a425d326
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts exists nat mul mem adjoin e048a425d326 construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts exists nat mul mem adjoin e048a425d326 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L76-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L76-L102

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

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_adjoin_e048a425d326 [CharZero K'] {S : Set K'} {x : K'} (hx : x ∈ Algebra.adjoin ℚ S) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ Algebra.adjoin ℤ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«exists_nat_mul_mem_adjoin» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_adjoin_e048a425d326
