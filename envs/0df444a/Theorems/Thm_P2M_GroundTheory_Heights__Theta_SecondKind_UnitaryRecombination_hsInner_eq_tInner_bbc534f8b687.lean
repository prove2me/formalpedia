-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_eq_tInner_bbc534f8b687
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_eq_tInner_bbc534f8b687
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:57.462812+00:00
-- url     : https://prove2.me/theorems/04161f09-4f91-486e-97e8-8b4f11dc51c0
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner eq t Inner bbc534f8b687: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner eq t Inner bbc534f8b6
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner eq t Inner bbc534f8b687 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner eq t Inner bbc534f8b687 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L362-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L362-L367

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_eq_tInner_bbc534f8b687 {k : Fin F.dim} {τ : Fin F.f} (hk : F.place k = τ) (X : MatProd F.p F.q) :
    hsInner (F.E k) X = tInner (F.E k τ) (X τ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsInner_eq_tInner» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_eq_tInner_bbc534f8b687
