-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Gi_mul_G_c5650003a984
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Gi_mul_G_c5650003a984
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:01.509621+00:00
-- url     : https://prove2.me/theorems/715082d3-6ced-5966-9c25-200c93b8dc52
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Gi mul G c5650003a984: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Gi mul G c5650003a984
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Gi mul G c5650003a984 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Gi mul G c5650003a984 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L492-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L492-L501

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Gi_mul_G_c5650003a984 (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) : Gi F y τ k * G F y τ k = 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«Gi_mul_G» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Gi_mul_G_c5650003a984
