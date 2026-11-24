-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_comm_a8b0e44bf3d7
-- name    : P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_comm_a8b0e44bf3d7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:24.556026+00:00
-- url     : https://prove2.me/theorems/44484978-49ae-42f8-b864-eaf4f2a5301b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Gram re inner comm a8b0e44bf3d7: P2 M Ground Theory Heights  Heights Chart Gram re inner comm a8b0e44bf3d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Gram re inner comm a8b0e44bf3d7 construction uses the P2 M Ground Theory Heights  Heights Chart Gram re inner comm a8b0e44bf3d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L26-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped InnerProductSpace
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_comm_a8b0e44bf3d7 (x z : F) : (⟪x, z⟫_ℂ).re = (⟪z, x⟫_ℂ).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartGram».«re_inner_comm» := P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_comm_a8b0e44bf3d7
