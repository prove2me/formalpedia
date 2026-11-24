-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInnerR_apply_7b3216fb2db8
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInnerR_apply_7b3216fb2db8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:48.122797+00:00
-- url     : https://prove2.me/theorems/f62a72da-cc89-4102-861e-768c84abcd50
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner R apply 7b3216fb2db8: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner R apply 7b3216fb2db8
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner R apply 7b3216fb2db8 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner R apply 7b3216fb2db8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L116-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L116-L116

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInnerR_apply_7b3216fb2db8 (X Y : MatProd p q) : hsInnerR X Y = hsInner X Y := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsInnerR_apply» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInnerR_apply_7b3216fb2db8
