-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_io_coords_bb82a2b1c0fb
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_io_coords_bb82a2b1c0fb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:51.53948+00:00
-- url     : https://prove2.me/theorems/fb9bea3d-99d9-4544-b58c-c742d4b4fecb
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination io coords bb82a2b1c0fb: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination io coords bb82a2b1c0fb
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination io coords bb82a2b1c0fb construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination io coords bb82a2b1c0fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L157-L161

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_io_coords_bb82a2b1c0fb (F : OrthoFrame) {X : MatProd F.p F.q} (hX : X ∈ lieProd F.p F.q) : F.io (coords F X) = X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«io_coords» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_io_coords_bb82a2b1c0fb
