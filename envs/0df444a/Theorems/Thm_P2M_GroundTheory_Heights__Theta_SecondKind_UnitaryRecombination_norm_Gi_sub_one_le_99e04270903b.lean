-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Gi_sub_one_le_99e04270903b
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Gi_sub_one_le_99e04270903b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:20.122804+00:00
-- url     : https://prove2.me/theorems/4abaa61b-5285-4953-90a5-12e84e555410
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm Gi sub one le 99e04270903b: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm Gi sub one le 99e04270903b
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm Gi sub one le 99e04270903b construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm Gi sub one le 99e04270903b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L632-L661
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L632-L661

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Gi_sub_one_le_99e04270903b (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) :
    ‖Gi F y τ k - 1‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) - 1 ∧
      ‖Gi F y τ k‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«norm_Gi_sub_one_le» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Gi_sub_one_le_99e04270903b
