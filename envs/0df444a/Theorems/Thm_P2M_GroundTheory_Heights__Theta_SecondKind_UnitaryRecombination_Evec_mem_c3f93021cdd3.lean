-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Evec_mem_c3f93021cdd3
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Evec_mem_c3f93021cdd3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:28.796852+00:00
-- url     : https://prove2.me/theorems/574ad92a-9c9b-430e-a39c-498985b08c36
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Evec mem c3f93021cdd3: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Evec mem c3f93021cdd3
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Evec mem c3f93021cdd3 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Evec mem c3f93021cdd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L476-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L476-L479

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Evec_mem_c3f93021cdd3 (τ : Fin F.f) (m : ℕ) : Evec F τ m ∈ indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«Evec_mem» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Evec_mem_c3f93021cdd3
