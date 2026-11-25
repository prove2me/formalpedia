-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineIndexAlt_genIndex_span_eq_finprod_082c844d81d2
-- name    : P2M_GroundTheory_Heights__Heights_DualLineIndexAlt_genIndex_span_eq_finprod_082c844d81d2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:42:09.025208+00:00
-- url     : https://prove2.me/theorems/560bc0db-df7d-49a7-af48-37a09e69520c
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Index Alt gen Index span eq finprod 082c844d81d2: P2 M Ground Theory Heights  Heights Dual Line Index Alt gen Index span eq finprod 082c844d81d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Index Alt gen Index span eq finprod 082c844d81d2 construction uses the P2 M Ground Theory Heights  Heights Dual Line Index Alt gen Index span eq finprod 082c844d81d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineIndex.lean#L16-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineIndex.lean#L16-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineIdealDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIdealIndexPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineIndex
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
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineIndexAlt

theorem P2M_GroundTheory_Heights__Heights_DualLineIndexAlt_genIndex_span_eq_finprod_082c844d81d2 {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι] {y : ι → L}
    (hy : y ≠ 0) :
    genIndex (Submodule.span (𝓞 L) (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup =
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineIndexAlt».«genIndex_span_eq_finprod» := P2M_GroundTheory_Heights__Heights_DualLineIndexAlt_genIndex_span_eq_finprod_082c844d81d2
