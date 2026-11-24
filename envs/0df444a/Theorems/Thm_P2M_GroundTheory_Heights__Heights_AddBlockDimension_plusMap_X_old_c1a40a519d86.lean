-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_old_c1a40a519d86
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_old_c1a40a519d86
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:53.979363+00:00
-- url     : https://prove2.me/theorems/d7fa0000-59ed-4ef6-8e56-9f71dc2845f3
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Dimension plus Map X old c1a40a519d86: P2 M Ground Theory Heights  Heights Add Block Dimension plus Map X old c1a40a519d86
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Dimension plus Map X old c1a40a519d86 construction uses the P2 M Ground Theory Heights  Heights Add Block Dimension plus Map X old c1a40a519d86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L24-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockDimension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_old_c1a40a519d86 (v : Coord n) :
    plusMap D (X (D.oldCoord v)) = C (P.mkF (X v)) * X (some v.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockDimension».«plusMap_X_old» := P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_old_c1a40a519d86
