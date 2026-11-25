-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_plusMap_c2ff32dcee6d
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_plusMap_c2ff32dcee6d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:44.335361+00:00
-- url     : https://prove2.me/theorems/8f71d021-6849-4927-bc49-4ce88820bfc5
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Dimension ker plus Map c2ff32dcee6d: P2 M Ground Theory Heights  Heights Add Block Dimension ker plus Map c2ff32dcee6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Dimension ker plus Map c2ff32dcee6d construction uses the P2 M Ground Theory Heights  Heights Add Block Dimension ker plus Map c2ff32dcee6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L22-L22

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_plusMap_c2ff32dcee6d : RingHom.ker (plusMap D) = D.extIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockDimension».«ker_plusMap» := P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_plusMap_c2ff32dcee6d
