-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_E_E_d7a9c5da1e23
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_E_E_d7a9c5da1e23
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:42.811963+00:00
-- url     : https://prove2.me/theorems/53db17ae-d755-4556-a83c-9b650a8cf196
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner E E d7a9c5da1e23: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner E E d7a9c5da1e23
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner E E d7a9c5da1e23 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner E E d7a9c5da1e23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L369-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L369-L371

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_E_E_d7a9c5da1e23 {k : Fin F.dim} {τ : Fin F.f} (hk : F.place k = τ) (l : Fin F.dim) :
    tInner (F.E k τ) (F.E l τ) = if k = l then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«tInner_E_E» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_E_E_d7a9c5da1e23
