-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_nonneg_1a2c98d71290
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_nonneg_1a2c98d71290
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:34.946354+00:00
-- url     : https://prove2.me/theorems/07927dbd-bb0c-4a2c-8748-b7da8932bc79
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs nonneg 1a2c98d71290: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs nonneg 1a2c98d71290
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs nonneg 1a2c98d71290 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs nonneg 1a2c98d71290 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L30-L30

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_nonneg_1a2c98d71290 (X : Matrix ι ι ℂ) : 0 ≤ hs X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hs_nonneg» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_nonneg_1a2c98d71290
