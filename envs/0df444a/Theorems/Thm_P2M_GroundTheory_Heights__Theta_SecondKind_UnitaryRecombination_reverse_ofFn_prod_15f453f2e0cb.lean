-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_reverse_ofFn_prod_15f453f2e0cb
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_reverse_ofFn_prod_15f453f2e0cb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:08.155073+00:00
-- url     : https://prove2.me/theorems/2dab05f0-009e-4736-840a-bc5832d1c955
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination reverse of Fn prod 15f453f2e0cb: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination reverse of Fn prod 15f453f2e0cb
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination reverse of Fn prod 15f453f2e0cb construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination reverse of Fn prod 15f453f2e0cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L506-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L506-L516

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_reverse_ofFn_prod_15f453f2e0cb (y : Fin F.dim → ℝ) (τ : Fin F.f) (n : ℕ) :
    ((List.ofFn fun l : Fin n => NormedSpace.exp (yy F y l • Evec F τ l)).reverse).prod =
      G F y τ n := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«reverse_ofFn_prod» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_reverse_ofFn_prod_15f453f2e0cb
