-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_eq_sum_sq_8a8bb0ebef43
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_eq_sum_sq_8a8bb0ebef43
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:21.797183+00:00
-- url     : https://prove2.me/theorems/2bd0dc02-9fa7-435f-b811-d4e8c45ba9d2
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner self eq sum sq 8a8bb0ebef43: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner self eq sum sq 8a
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner self eq sum sq 8a8bb0ebef43 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination hs Inner self eq sum sq 8a8bb0ebef43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L170-L174

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

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_eq_sum_sq_8a8bb0ebef43 (F : OrthoFrame) {X : MatProd F.p F.q} (hX : X ∈ lieProd F.p F.q) :
    hsInner X X = ∑ k, coords F X k ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«hsInner_self_eq_sum_sq» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_self_eq_sum_sq_8a8bb0ebef43
