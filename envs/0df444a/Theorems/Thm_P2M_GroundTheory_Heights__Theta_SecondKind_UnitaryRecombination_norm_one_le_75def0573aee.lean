-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_one_le_75def0573aee
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_one_le_75def0573aee
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:57.883801+00:00
-- url     : https://prove2.me/theorems/71fafc41-a6b9-4544-9150-a6de83802246
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm one le 75def0573aee: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm one le 75def0573aee
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm one le 75def0573aee construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm one le 75def0573aee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L567-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L567-L569

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_one_le_75def0573aee {ι : Type*} [Fintype ι] [DecidableEq ι] : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«norm_one_le» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_one_le_75def0573aee
