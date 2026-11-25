-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_oldMap_e83711f0f9ca
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_oldMap_e83711f0f9ca
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:34.136699+00:00
-- url     : https://prove2.me/theorems/c078c0c9-376a-4b16-ae02-94a79de296fe
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Dimension ker old Map e83711f0f9ca: P2 M Ground Theory Heights  Heights Add Block Dimension ker old Map e83711f0f9ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Dimension ker old Map e83711f0f9ca construction uses the P2 M Ground Theory Heights  Heights Add Block Dimension ker old Map e83711f0f9ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L52-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L52-L71

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_oldMap_e83711f0f9ca : RingHom.ker (oldMap D) = P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockDimension».«ker_oldMap» := P2M_GroundTheory_Heights__Heights_AddBlockDimension_ker_oldMap_e83711f0f9ca
