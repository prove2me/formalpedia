-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_yy_val_5dc3d3ca6f25
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_yy_val_5dc3d3ca6f25
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:47.986894+00:00
-- url     : https://prove2.me/theorems/47085c9c-e861-454d-a0e8-b9360e1b14c2
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination yy val 5dc3d3ca6f25: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination yy val 5dc3d3ca6f25
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination yy val 5dc3d3ca6f25 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination yy val 5dc3d3ca6f25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L473-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L473-L474

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_yy_val_5dc3d3ca6f25 (y : Fin F.dim → ℝ) (l : Fin F.dim) : yy F y l = y l := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«yy_val» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_yy_val_5dc3d3ca6f25
