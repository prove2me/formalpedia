-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_sum_card_Ioi_mul_two_69f2c1bd387d
-- name    : P2M_GroundTheory_Heights__Heights_KRest_sum_card_Ioi_mul_two_69f2c1bd387d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:44.093671+00:00
-- url     : https://prove2.me/theorems/a84171a1-72e7-4e2f-9b88-37882f577d66
-- title:
--   P2 M Ground Theory Heights  Heights KRest sum card Ioi mul two 69f2c1bd387d: P2 M Ground Theory Heights  Heights KRest sum card Ioi mul two 69f2c1bd387d
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest sum card Ioi mul two 69f2c1bd387d construction uses the P2 M Ground Theory Heights  Heights KRest sum card Ioi mul two 69f2c1bd387d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L71-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KRest_sum_card_Ioi_mul_two_69f2c1bd387d (N : ℕ) :
    (∑ i : Fin N, (Finset.Ioi i).card) * 2 = N * (N - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«sum_card_Ioi_mul_two» := P2M_GroundTheory_Heights__Heights_KRest_sum_card_Ioi_mul_two_69f2c1bd387d
