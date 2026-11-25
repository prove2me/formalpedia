-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_8815a8a2ccae
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_8815a8a2ccae
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:35.509596+00:00
-- url     : https://prove2.me/theorems/d637956e-0201-45ee-b791-90c7aa911fb0
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E mem 8815a8a2ccae: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E mem 8815a8a2ccae
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E mem 8815a8a2ccae construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination E mem 8815a8a2ccae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L150-L151

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_8815a8a2ccae (F : OrthoFrame) (l : Fin F.dim) : F.E l ∈ lieProd F.p F.q := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«E_mem» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_8815a8a2ccae
