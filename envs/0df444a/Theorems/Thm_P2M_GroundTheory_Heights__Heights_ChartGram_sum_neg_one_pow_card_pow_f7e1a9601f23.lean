-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_sum_neg_one_pow_card_pow_f7e1a9601f23
-- name    : P2M_GroundTheory_Heights__Heights_ChartGram_sum_neg_one_pow_card_pow_f7e1a9601f23
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:31.240224+00:00
-- url     : https://prove2.me/theorems/e860aa77-25f0-424e-9ece-afd20edb8048
-- title:
--   P2 M Ground Theory Heights  Heights Chart Gram sum neg one pow card pow f7e1a9601f23: P2 M Ground Theory Heights  Heights Chart Gram sum neg one pow card pow f7e1a9601f23
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Gram sum neg one pow card pow f7e1a9601f23 construction uses the P2 M Ground Theory Heights  Heights Chart Gram sum neg one pow card pow f7e1a9601f23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramPolar.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramPolar.lean#L12-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Finset
open ReciprocityTheory.ChartRestriction.G.Geo (mixedDisc)

theorem P2M_GroundTheory_Heights__Heights_ChartGram_sum_neg_one_pow_card_pow_f7e1a9601f23 (D : ℕ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartGram».«sum_neg_one_pow_card_pow» := P2M_GroundTheory_Heights__Heights_ChartGram_sum_neg_one_pow_card_pow_f7e1a9601f23
