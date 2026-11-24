-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_card_place_2ef5794d3fc9
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_card_place_2ef5794d3fc9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:23.034437+00:00
-- url     : https://prove2.me/theorems/907666b0-786d-4256-be26-ef2727215852
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination card place 2ef5794d3fc9: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination card place 2ef5794d3fc9
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination card place 2ef5794d3fc9 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination card place 2ef5794d3fc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L401-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L401-L425

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
variable {ι : Type*} [Fintype ι]
variable (F : OrthoFrame)

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_card_place_2ef5794d3fc9 (τ : Fin F.f) : Fintype.card {l // F.place l = τ} = F.r ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«card_place» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_card_place_2ef5794d3fc9
