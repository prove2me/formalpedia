-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_zero_0d832980d7e3
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_zero_0d832980d7e3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:24.922824+00:00
-- url     : https://prove2.me/theorems/dd1b3ee1-8802-470c-a61f-a1a455ae69ef
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs zero 0d832980d7e3: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs zero 0d832980d7e3
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs zero 0d832980d7e3 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs zero 0d832980d7e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L38-L39

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_zero_0d832980d7e3 : hs (0 : Matrix ι ι ℂ) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hs_zero» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_zero_0d832980d7e3
