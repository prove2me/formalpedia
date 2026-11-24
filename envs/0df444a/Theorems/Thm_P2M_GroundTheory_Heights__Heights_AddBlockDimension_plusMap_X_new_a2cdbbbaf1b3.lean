-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_new_a2cdbbbaf1b3
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_new_a2cdbbbaf1b3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:18.34752+00:00
-- url     : https://prove2.me/theorems/8d37c96b-871c-4e9a-a22d-3eecda189ee1
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Dimension plus Map X new a2cdbbbaf1b3: P2 M Ground Theory Heights  Heights Add Block Dimension plus Map X new a2cdbbbaf1b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Dimension plus Map X new a2cdbbbaf1b3 construction uses the P2 M Ground Theory Heights  Heights Add Block Dimension plus Map X new a2cdbbbaf1b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_new_a2cdbbbaf1b3 (j : Fin (D.size + 1)) :
    plusMap D (X (D.newCoord j)) = C (D.elt j) * X none := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockDimension».«plusMap_X_new» := P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_new_a2cdbbbaf1b3
