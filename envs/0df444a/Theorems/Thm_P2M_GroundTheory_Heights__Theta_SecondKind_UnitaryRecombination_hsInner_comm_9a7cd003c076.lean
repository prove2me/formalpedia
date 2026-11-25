-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_comm_9a7cd003c076
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_comm_9a7cd003c076
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:42.639026+00:00
-- url     : https://prove2.me/theorems/ad68da6f-71f2-4221-87ab-661e60a4fcf9
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner comm 9a7cd003c076: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner comm 9a7cd003c076
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner comm 9a7cd003c076 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner comm 9a7cd003c076 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L104-L105

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_comm_9a7cd003c076 (X Y : MatProd p q) : hsInner X Y = hsInner Y X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsInner_comm» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_comm_9a7cd003c076
