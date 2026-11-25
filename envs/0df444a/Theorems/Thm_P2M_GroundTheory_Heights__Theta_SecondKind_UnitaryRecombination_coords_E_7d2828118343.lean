-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_E_7d2828118343
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_E_7d2828118343
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:01.525691+00:00
-- url     : https://prove2.me/theorems/c0716e62-d91c-5db3-aa8b-aaf6886290eb
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coords E 7d2828118343: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coords E 7d2828118343
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coords E 7d2828118343 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coords E 7d2828118343 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L145-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L145-L148

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_E_7d2828118343 (F : OrthoFrame) (l : Fin F.dim) : coords F (F.E l) = Pi.single l 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«coords_E» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coords_E_7d2828118343
