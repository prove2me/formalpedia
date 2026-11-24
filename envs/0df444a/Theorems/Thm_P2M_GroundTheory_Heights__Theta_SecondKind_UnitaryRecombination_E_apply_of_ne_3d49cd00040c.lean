-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_apply_of_ne_3d49cd00040c
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_apply_of_ne_3d49cd00040c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:56.008894+00:00
-- url     : https://prove2.me/theorems/e077c2fd-1b2f-4b61-a768-330592a2f1e0
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E apply of ne 3d49cd00040c: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E apply of ne 3d49cd00040c
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E apply of ne 3d49cd00040c construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E apply of ne 3d49cd00040c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L176-L177

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_apply_of_ne_3d49cd00040c (F : OrthoFrame) {l : Fin F.dim} {τ : Fin F.f} (h : τ ≠ F.place l) : F.E l τ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«E_apply_of_ne» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_apply_of_ne_3d49cd00040c
