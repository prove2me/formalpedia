-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_blockWeight_69a38f0cbb39
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_blockWeight_69a38f0cbb39
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:05:26.805082+00:00
-- url     : https://prove2.me/theorems/f4262bd3-bc3a-5ce5-9831-2d8ee0192c8a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers prod pow block Weight 69a38f0cbb39: P2 M Ground Theory Heights  Heights Field Numbers prod pow block Weight 69a38f0cbb39
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers prod pow block Weight 69a38f0cbb39 construction uses the P2 M Ground Theory Heights  Heights Field Numbers prod pow block Weight 69a38f0cbb39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartDehomog.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartDehomog.lean#L13-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartDehomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_blockWeight_69a38f0cbb39 {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {M : Type*}
    [CommMonoid M] (w : K → M) (e : (Σ k, ι k) →₀ ℕ) :
    ∏ k, w k ^ (Finsupp.weight (blockWeight ι) e k) = e.prod fun v n => w v.1 ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«prod_pow_blockWeight» := P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_blockWeight_69a38f0cbb39
