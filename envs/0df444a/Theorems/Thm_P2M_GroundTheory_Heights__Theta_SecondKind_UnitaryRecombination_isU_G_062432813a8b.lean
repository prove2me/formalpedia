-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_G_062432813a8b
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_G_062432813a8b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:54.518456+00:00
-- url     : https://prove2.me/theorems/ee764dd4-852b-5efb-aca1-1c390931561d
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U G 062432813a8b: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U G 062432813a8b
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U G 062432813a8b construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination is U G 062432813a8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L541-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L541-L544

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_G_062432813a8b (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) : IsU (G F y τ k) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«isU_G» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_G_062432813a8b
