-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_sum_Icc_one_eq_sum_fin_6fc36c803c22
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_sum_Icc_one_eq_sum_fin_6fc36c803c22
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:00.637806+00:00
-- url     : https://prove2.me/theorems/274da960-ba57-5fa3-8893-86d899f6f89e
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms sum Icc one eq sum fin 6fc36c803c22: P2 M Ground Theory Heights  Heights Rest Terms sum Icc one eq sum fin 6fc36c803c22
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms sum Icc one eq sum fin 6fc36c803c22 construction uses the P2 M Ground Theory Heights  Heights Rest Terms sum Icc one eq sum fin 6fc36c803c22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagPowerSumPreimage.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagPowerSumPreimage.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagPowerSumPreimage
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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_sum_Icc_one_eq_sum_fin_6fc36c803c22 {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ l ∈ Finset.Icc 1 N, g l = ∑ i : Fin N, g (i.val + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«sum_Icc_one_eq_sum_fin» := P2M_GroundTheory_Heights__Heights_RestTerms_sum_Icc_one_eq_sum_fin_6fc36c803c22
