-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_cc_nonneg_87c80e7e3807
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_cc_nonneg_87c80e7e3807
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:39.926271+00:00
-- url     : https://prove2.me/theorems/4d218867-9fcd-456e-a267-dcd293f9fc15
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination cc nonneg 87c80e7e3807: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination cc nonneg 87c80e7e3807
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination cc nonneg 87c80e7e3807 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination cc nonneg 87c80e7e3807 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L574-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L574-L575

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_cc_nonneg_87c80e7e3807 (y : Fin F.dim → ℝ) (τ : Fin F.f) (m : ℕ) : 0 ≤ cc F y τ m := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«cc_nonneg» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_cc_nonneg_87c80e7e3807
