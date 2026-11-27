-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_sub_1075cf7fe718
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_sub_1075cf7fe718
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:44.960844+00:00
-- url     : https://prove2.me/theorems/8d3e2788-40e0-5ab4-bf85-510b6cf81751
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Vec sub 1075cf7fe718: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Vec sub 1075cf7fe718
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Vec sub 1075cf7fe718 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Vec sub 1075cf7fe718 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L27-L27

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_sub_1075cf7fe718 (X Y : Matrix ι ι ℂ) : hsVec (X - Y) = hsVec X - hsVec Y := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsVec_sub» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_sub_1075cf7fe718
