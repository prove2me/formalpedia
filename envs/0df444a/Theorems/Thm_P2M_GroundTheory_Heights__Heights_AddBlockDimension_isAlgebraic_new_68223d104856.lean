-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_isAlgebraic_new_68223d104856
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockDimension_isAlgebraic_new_68223d104856
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:06.817983+00:00
-- url     : https://prove2.me/theorems/b7c4dfcb-ea25-420c-813b-1bd1f0c7de9f
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Dimension is Algebraic new 68223d104856: P2 M Ground Theory Heights  Heights Add Block Dimension is Algebraic new 68223d104856
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Dimension is Algebraic new 68223d104856 construction uses the P2 M Ground Theory Heights  Heights Add Block Dimension is Algebraic new 68223d104856 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L73-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicNew.lean#L73-L121

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockDimension_isAlgebraic_new_68223d104856 [CharZero P.FunField] {j : Fin (D.size + 1)} (hj : D.elt j ≠ 0)
    (i : Fin (D.size + 1)) :
    IsAlgebraic (Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
      (Set.range fun v ↦ oldMap D (X v)))) (plusMap D (X (D.newCoord i))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockDimension».«isAlgebraic_new» := P2M_GroundTheory_Heights__Heights_AddBlockDimension_isAlgebraic_new_68223d104856
