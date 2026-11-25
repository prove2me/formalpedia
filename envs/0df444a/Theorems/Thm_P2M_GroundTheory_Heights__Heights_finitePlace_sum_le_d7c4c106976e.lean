-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finitePlace_sum_le_d7c4c106976e
-- name    : P2M_GroundTheory_Heights__Heights_finitePlace_sum_le_d7c4c106976e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:53.262735+00:00
-- url     : https://prove2.me/theorems/150491ba-f974-591f-87f1-8d15b79a4a67
-- title:
--   P2 M Ground Theory Heights  Heights finite Place sum le d7c4c106976e: P2 M Ground Theory Heights  Heights finite Place sum le d7c4c106976e
-- statement:
--   The P2 M Ground Theory Heights  Heights finite Place sum le d7c4c106976e construction uses the P2 M Ground Theory Heights  Heights finite Place sum le d7c4c106976e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterLe.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterLe.lean#L10-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterLe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitePlaceSumLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterLe
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
open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_finitePlace_sum_le_d7c4c106976e {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) {α : Type*}
    (s : Finset α) (f : α → K) {B : ℝ} (hB : 0 ≤ B) (h : ∀ a ∈ s, v (f a) ≤ B) :
    v (∑ a ∈ s, f a) ≤ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finitePlace_sum_le» := P2M_GroundTheory_Heights__Heights_finitePlace_sum_le_d7c4c106976e
