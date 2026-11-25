-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_left_c312c8f11683
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_left_c312c8f11683
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:57.219367+00:00
-- url     : https://prove2.me/theorems/469a1cd3-bbc7-42a7-8a25-b7e85e2849e8
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner sum left c312c8f11683: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner sum left c312c8f11683
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner sum left c312c8f11683 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner sum left c312c8f11683 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L123-L126

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
variable {f : ℕ} {p q : Fin f → ℕ}

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_left_c312c8f11683 {κ : Type*} (s : Finset κ) (X : MatProd p q) (c : κ → ℝ)
    (Y : κ → MatProd p q) : hsInner (∑ m ∈ s, c m • Y m) X = ∑ m ∈ s, c m * hsInner (Y m) X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsInner_sum_left» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_left_c312c8f11683
