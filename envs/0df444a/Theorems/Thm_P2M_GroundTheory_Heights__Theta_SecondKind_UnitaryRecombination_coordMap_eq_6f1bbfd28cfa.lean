-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coordMap_eq_6f1bbfd28cfa
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coordMap_eq_6f1bbfd28cfa
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:55.426517+00:00
-- url     : https://prove2.me/theorems/aef2a22f-a0e0-534f-bc01-2a678374e6a3
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coord Map eq 6f1bbfd28cfa: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coord Map eq 6f1bbfd28cfa
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coord Map eq 6f1bbfd28cfa construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination coord Map eq 6f1bbfd28cfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L518-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L518-L522

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coordMap_eq_6f1bbfd28cfa (y : Fin F.dim → ℝ) (τ : Fin F.f) : F.coordMap y τ = G F y τ F.dim := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«coordMap_eq» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_coordMap_eq_6f1bbfd28cfa
