-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_add_4710712abb39
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_add_4710712abb39
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:47.404879+00:00
-- url     : https://prove2.me/theorems/6a8737ae-ee1d-4ebb-88ce-a066e8060e20
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Vec add 4710712abb39: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Vec add 4710712abb39
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Vec add 4710712abb39 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Vec add 4710712abb39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L26-L26

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_add_4710712abb39 (X Y : Matrix ι ι ℂ) : hsVec (X + Y) = hsVec X + hsVec Y := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsVec_add» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsVec_add_4710712abb39
