-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_sq_0bd4fc15945c
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_sq_0bd4fc15945c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:39.293801+00:00
-- url     : https://prove2.me/theorems/9e9e9122-8ce5-4d05-b295-8c0882e5d1fa
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs sq 0bd4fc15945c: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs sq 0bd4fc15945c
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs sq 0bd4fc15945c construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs sq 0bd4fc15945c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L41-L42

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_sq_0bd4fc15945c (X : Matrix ι ι ℂ) : hs X ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hs_sq» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_sq_0bd4fc15945c
