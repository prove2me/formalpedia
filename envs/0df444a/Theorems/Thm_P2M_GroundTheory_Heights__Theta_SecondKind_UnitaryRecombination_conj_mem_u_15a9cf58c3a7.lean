-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_conj_mem_u_15a9cf58c3a7
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_conj_mem_u_15a9cf58c3a7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:38.782789+00:00
-- url     : https://prove2.me/theorems/6b0d3b28-2d91-4d96-b229-8aaecd8fa14f
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination conj mem u 15a9cf58c3a7: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination conj mem u 15a9cf58c3a7
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination conj mem u 15a9cf58c3a7 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination conj mem u 15a9cf58c3a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L546-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L546-L565

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_conj_mem_u_15a9cf58c3a7 {p q : ℕ} {g h X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsU g)
    (hgh : g * h = 1) (hX : X ∈ indefiniteUnitaryLieAlgebra p q) :
    h * X * g ∈ indefiniteUnitaryLieAlgebra p q := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«conj_mem_u» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_conj_mem_u_15a9cf58c3a7
