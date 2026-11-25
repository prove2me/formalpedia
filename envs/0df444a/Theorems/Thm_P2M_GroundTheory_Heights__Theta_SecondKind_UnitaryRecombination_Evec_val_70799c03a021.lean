-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Evec_val_70799c03a021
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Evec_val_70799c03a021
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:12.214871+00:00
-- url     : https://prove2.me/theorems/16795a11-d187-43a2-833b-910a46b65897
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Evec val 70799c03a021: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Evec val 70799c03a021
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Evec val 70799c03a021 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination Evec val 70799c03a021 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L470-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L470-L471

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Evec_val_70799c03a021 (τ : Fin F.f) (l : Fin F.dim) : Evec F τ l = F.E l τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«Evec_val» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_Evec_val_70799c03a021
