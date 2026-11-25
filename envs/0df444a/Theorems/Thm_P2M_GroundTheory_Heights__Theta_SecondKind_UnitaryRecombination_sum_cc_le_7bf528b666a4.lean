-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_cc_le_7bf528b666a4
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_cc_le_7bf528b666a4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:31.771333+00:00
-- url     : https://prove2.me/theorems/edbe13f0-4a54-4952-9c69-2a75d26979cc
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination sum cc le 7bf528b666a4: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination sum cc le 7bf528b666a4
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination sum cc le 7bf528b666a4 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination sum cc le 7bf528b666a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L663-L678
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L663-L678

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_cc_le_7bf528b666a4 (y : Fin F.dim → ℝ) (τ : Fin F.f) {a : ℝ} (hy : ∀ l, |y l| ≤ a) {k : ℕ}
    (hk : k ≤ F.dim) : ∑ m ∈ Finset.range k, cc F y τ m ≤ (F.r : ℝ) ^ 2 * a := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«sum_cc_le» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_cc_le_7bf528b666a4
