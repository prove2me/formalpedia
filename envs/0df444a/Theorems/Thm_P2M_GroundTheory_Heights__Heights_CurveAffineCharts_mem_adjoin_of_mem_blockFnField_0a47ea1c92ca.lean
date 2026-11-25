-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_adjoin_of_mem_blockFnField_0a47ea1c92ca
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_adjoin_of_mem_blockFnField_0a47ea1c92ca
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:26.672884+00:00
-- url     : https://prove2.me/theorems/55d28c1b-1179-5016-a633-0bac8d4f03cf
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts mem adjoin of mem block Fn Field 0a47ea1c92ca: P2 M Ground Theory Heights  Heights Curve Affine Charts mem adjoin of mem block Fn Field 0a47ea1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts mem adjoin of mem block Fn Field 0a47ea1c92ca construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts mem adjoin of mem block Fn Field 0a47ea1c92ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L106-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L106-L123

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
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_adjoin_of_mem_blockFnField_0a47ea1c92ca [NumberField K'] (t : T) (ht : y ⟨(), t⟩ ≠ 0) {x : K'}
    (hx : x ∈ blockFnField y) :
    x ∈ Algebra.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«mem_adjoin_of_mem_blockFnField» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_adjoin_of_mem_blockFnField_0a47ea1c92ca
