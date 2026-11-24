-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_right_420d47d25329
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_right_420d47d25329
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:04.298565+00:00
-- url     : https://prove2.me/theorems/12cd9492-19f4-47f5-bb94-0a72aa9fb1da
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner sum right 420d47d25329: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner sum right 420d47d25329
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner sum right 420d47d25329 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner sum right 420d47d25329 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L118-L121

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_right_420d47d25329 {κ : Type*} (s : Finset κ) (X : MatProd p q) (c : κ → ℝ)
    (Y : κ → MatProd p q) : hsInner X (∑ m ∈ s, c m • Y m) = ∑ m ∈ s, c m * hsInner X (Y m) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsInner_sum_right» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_sum_right_420d47d25329
