-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_le_cae1f6c984d7
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_le_cae1f6c984d7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:04.022435+00:00
-- url     : https://prove2.me/theorems/a8192f87-2aca-4d58-a807-8685b998b2c8
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm exp le cae1f6c984d7: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm exp le cae1f6c984d7
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm exp le cae1f6c984d7 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination norm exp le cae1f6c984d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L210-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L210-L215

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_le_cae1f6c984d7 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«norm_exp_le» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_le_cae1f6c984d7
