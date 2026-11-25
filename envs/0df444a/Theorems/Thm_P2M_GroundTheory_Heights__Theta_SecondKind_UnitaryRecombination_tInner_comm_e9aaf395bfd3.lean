-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_comm_e9aaf395bfd3
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_comm_e9aaf395bfd3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:01.283681+00:00
-- url     : https://prove2.me/theorems/ca58474b-f788-40dd-b552-0a96e4e13502
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner comm e9aaf395bfd3: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner comm e9aaf395bfd3
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner comm e9aaf395bfd3 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner comm e9aaf395bfd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L97-L100

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
variable {f : ℕ} {p q : Fin f → ℕ}

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_comm_e9aaf395bfd3 {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) : tInner X Y = tInner Y X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«tInner_comm» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_comm_e9aaf395bfd3
