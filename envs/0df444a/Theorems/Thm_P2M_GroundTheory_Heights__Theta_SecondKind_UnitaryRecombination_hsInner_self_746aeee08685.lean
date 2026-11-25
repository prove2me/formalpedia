-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_746aeee08685
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_746aeee08685
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:27.530639+00:00
-- url     : https://prove2.me/theorems/51b02108-35f6-56d9-af59-9e225e2558a8
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner self 746aeee08685: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner self 746aeee08685
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner self 746aeee08685 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner self 746aeee08685 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L131-L132

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_746aeee08685 (X : MatProd p q) : hsInner X X = ∑ τ, hs (X τ) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsInner_self» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_746aeee08685
