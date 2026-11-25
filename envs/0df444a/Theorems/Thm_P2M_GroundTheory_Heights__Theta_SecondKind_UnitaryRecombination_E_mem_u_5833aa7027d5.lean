-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_u_5833aa7027d5
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_u_5833aa7027d5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:38.244234+00:00
-- url     : https://prove2.me/theorems/c816abce-05e5-4a85-95a1-a1a6aa724205
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E mem u 5833aa7027d5: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E mem u 5833aa7027d5
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E mem u 5833aa7027d5 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E mem u 5833aa7027d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L153-L155

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_u_5833aa7027d5 (F : OrthoFrame) (l : Fin F.dim) (τ : Fin F.f) :
    F.E l τ ∈ indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«E_mem_u» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_u_5833aa7027d5
