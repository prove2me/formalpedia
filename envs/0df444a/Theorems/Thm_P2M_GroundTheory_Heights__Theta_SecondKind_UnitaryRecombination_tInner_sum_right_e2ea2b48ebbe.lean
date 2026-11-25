-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_sum_right_e2ea2b48ebbe
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_sum_right_e2ea2b48ebbe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:59.822712+00:00
-- url     : https://prove2.me/theorems/58d21a21-4500-4525-be24-21fff11f66d0
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner sum right e2ea2b48ebbe: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner sum right e2ea2b48ebbe
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner sum right e2ea2b48ebbe construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner sum right e2ea2b48ebbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L355-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L355-L358

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
variable {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_sum_right_e2ea2b48ebbe {κ : Type*} (s : Finset κ) (X : Matrix ι ι ℂ) (c : κ → ℝ)
    (Y : κ → Matrix ι ι ℂ) : tInner X (∑ m ∈ s, c m • Y m) = ∑ m ∈ s, c m * tInner X (Y m) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«tInner_sum_right» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_sum_right_e2ea2b48ebbe
