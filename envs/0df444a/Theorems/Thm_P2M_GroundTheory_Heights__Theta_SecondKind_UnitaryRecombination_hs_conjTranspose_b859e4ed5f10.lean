-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_conjTranspose_b859e4ed5f10
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_conjTranspose_b859e4ed5f10
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:39.301969+00:00
-- url     : https://prove2.me/theorems/e8f277e6-2b69-4238-9fed-40cb846fc2e9
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs conj Transpose b859e4ed5f10: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs conj Transpose b859e4ed5f10
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs conj Transpose b859e4ed5f10 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs conj Transpose b859e4ed5f10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L54-L58

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_conjTranspose_b859e4ed5f10 (X : Matrix ι ι ℂ) : hs Xᴴ = hs X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hs_conjTranspose» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_conjTranspose_b859e4ed5f10
