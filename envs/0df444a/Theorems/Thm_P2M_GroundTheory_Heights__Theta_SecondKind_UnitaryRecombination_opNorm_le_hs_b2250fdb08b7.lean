-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_opNorm_le_hs_b2250fdb08b7
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_opNorm_le_hs_b2250fdb08b7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:00:17.711801+00:00
-- url     : https://prove2.me/theorems/31e9155f-fb4c-45c2-868b-e4310cdc72af
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination op Norm le hs b2250fdb08b7: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination op Norm le hs b2250fdb08b7
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination op Norm le hs b2250fdb08b7 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination op Norm le hs b2250fdb08b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L60-L71

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_opNorm_le_hs_b2250fdb08b7 (X : Matrix ι ι ℂ) : ‖X‖ ≤ hs X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«opNorm_le_hs» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_opNorm_le_hs_b2250fdb08b7
