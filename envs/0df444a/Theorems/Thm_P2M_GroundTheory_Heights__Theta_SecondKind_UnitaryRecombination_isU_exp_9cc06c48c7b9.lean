-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_exp_9cc06c48c7b9
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_exp_9cc06c48c7b9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:32.571346+00:00
-- url     : https://prove2.me/theorems/ee44712d-60a7-5f02-90b0-b823d22ec160
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U exp 9cc06c48c7b9: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U exp 9cc06c48c7b9
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U exp 9cc06c48c7b9 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U exp 9cc06c48c7b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L527-L531
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L527-L531

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable (F : OrthoFrame)

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_exp_9cc06c48c7b9 {p q : ℕ} {X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ indefiniteUnitaryLieAlgebra p q) : IsU (NormedSpace.exp X) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«isU_exp» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_exp_9cc06c48c7b9
