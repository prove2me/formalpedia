-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_G_sub_one_le_8a8a31fefc56
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_G_sub_one_le_8a8a31fefc56
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:12.344366+00:00
-- url     : https://prove2.me/theorems/38c6510b-4033-47ca-af17-7422d4859283
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm G sub one le 8a8a31fefc56: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm G sub one le 8a8a31fefc56
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm G sub one le 8a8a31fefc56 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm G sub one le 8a8a31fefc56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L601-L630
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L601-L630

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_G_sub_one_le_8a8a31fefc56 (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) :
    ‖G F y τ k - 1‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) - 1 ∧
      ‖G F y τ k‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«norm_G_sub_one_le» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_G_sub_one_le_8a8a31fefc56
