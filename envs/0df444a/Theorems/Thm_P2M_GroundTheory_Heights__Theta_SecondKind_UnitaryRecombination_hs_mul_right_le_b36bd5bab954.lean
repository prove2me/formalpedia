-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_mul_right_le_b36bd5bab954
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_mul_right_le_b36bd5bab954
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:25.279482+00:00
-- url     : https://prove2.me/theorems/fb9f73fe-fe2d-469f-b6a4-e79bc0111137
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs mul right le b36bd5bab954: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs mul right le b36bd5bab954
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs mul right le b36bd5bab954 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs mul right le b36bd5bab954 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L86-L89

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_mul_right_le_b36bd5bab954 (X B : Matrix ι ι ℂ) : hs (X * B) ≤ hs X * ‖B‖ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hs_mul_right_le» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_mul_right_le_b36bd5bab954
