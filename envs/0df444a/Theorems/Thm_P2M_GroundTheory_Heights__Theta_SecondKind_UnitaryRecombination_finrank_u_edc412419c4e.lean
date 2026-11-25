-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_finrank_u_edc412419c4e
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_finrank_u_edc412419c4e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:11.541317+00:00
-- url     : https://prove2.me/theorems/ec3954a2-f15b-5b0c-8a8f-e2953cfc3862
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination finrank u edc412419c4e: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination finrank u edc412419c4e
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination finrank u edc412419c4e construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination finrank u edc412419c4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L326-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L326-L330

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
variable (p q : ℕ)

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_finrank_u_edc412419c4e : Module.finrank ℝ (indefiniteUnitaryLieAlgebra p q) = (p + q) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«finrank_u» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_finrank_u_edc412419c4e
