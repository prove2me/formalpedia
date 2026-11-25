-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Evec_le_81ad8f9d2021
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Evec_le_81ad8f9d2021
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:38.604238+00:00
-- url     : https://prove2.me/theorems/96082657-44ec-5bf5-8d6f-16e359f418e2
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm Evec le 81ad8f9d2021: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm Evec le 81ad8f9d2021
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm Evec le 81ad8f9d2021 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm Evec le 81ad8f9d2021 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L577-L587
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L577-L587

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Evec_le_81ad8f9d2021 (τ : Fin F.f) (m : ℕ) : ‖Evec F τ m‖ ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«norm_Evec_le» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Evec_le_81ad8f9d2021
