-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_mul_0707742e5082
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_mul_0707742e5082
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:59.870923+00:00
-- url     : https://prove2.me/theorems/a6b3e1f9-1984-4e8e-9606-16868fb31124
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U mul 0707742e5082: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U mul 0707742e5082
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U mul 0707742e5082 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U mul 0707742e5082 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L533-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L533-L539

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_mul_0707742e5082 {p q : ℕ} {g h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsU g)
    (hh : IsU h) : IsU (g * h) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«isU_mul» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_mul_0707742e5082
