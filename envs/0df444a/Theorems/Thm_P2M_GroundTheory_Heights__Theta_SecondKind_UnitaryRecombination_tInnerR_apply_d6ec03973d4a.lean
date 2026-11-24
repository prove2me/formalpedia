-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInnerR_apply_d6ec03973d4a
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInnerR_apply_d6ec03973d4a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:48.771906+00:00
-- url     : https://prove2.me/theorems/e0ddbb27-43c3-42d3-88ad-bc9aec8c0847
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner R apply d6ec03973d4a: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner R apply d6ec03973d4a
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner R apply d6ec03973d4a construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination t Inner R apply d6ec03973d4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L349-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L349-L349

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInnerR_apply_d6ec03973d4a (X Y : Matrix ι ι ℂ) : tInnerR X Y = tInner X Y := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«tInnerR_apply» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInnerR_apply_d6ec03973d4a
