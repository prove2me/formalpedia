-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_io_58780eedfeee
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_io_58780eedfeee
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:43.779624+00:00
-- url     : https://prove2.me/theorems/7bc43c3e-9de1-45d9-8334-8e9ed773c965
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coords io 58780eedfeee: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coords io 58780eedfeee
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coords io 58780eedfeee construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coords io 58780eedfeee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L140-L143

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_io_58780eedfeee (F : OrthoFrame) (v : Fin F.dim → ℝ) : coords F (F.io v) = v := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«coords_io» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_io_58780eedfeee
