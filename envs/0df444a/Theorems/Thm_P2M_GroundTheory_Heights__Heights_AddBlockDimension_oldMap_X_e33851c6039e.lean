-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_X_e33851c6039e
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_X_e33851c6039e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:56.265197+00:00
-- url     : https://prove2.me/theorems/1ef1ee89-c88e-47ac-9364-d1d5c7236dfd
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Dimension old Map X e33851c6039e: P2 M Ground Theory Heights  Heights Add Block Dimension old Map X e33851c6039e
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Dimension old Map X e33851c6039e construction uses the P2 M Ground Theory Heights  Heights Add Block Dimension old Map X e33851c6039e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L32-L33

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_X_e33851c6039e (v : Coord n) : oldMap D (X v) = plusMap D (X (D.oldCoord v)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockDimension».«oldMap_X» := P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_X_e33851c6039e
