-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_exists_nat_of_bounds_a5ec014f4cda
-- name    : P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_exists_nat_of_bounds_a5ec014f4cda
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:33.074479+00:00
-- url     : https://prove2.me/theorems/518b184b-8ba6-425c-a331-5bcaad4b37cb
-- title:
--   P2 M Ground Theory Heights  Heights Component Of Inc Ideal exists nat of bounds a5ec014f4cda: P2 M Ground Theory Heights  Heights Component Of Inc Ideal exists nat of bounds a5ec014f4cda
-- statement:
--   The P2 M Ground Theory Heights  Heights Component Of Inc Ideal exists nat of bounds a5ec014f4cda construction uses the P2 M Ground Theory Heights  Heights Component Of Inc Ideal exists nat of bounds a5ec014f4cda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PComponentOfIncIdeal.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PComponentOfIncIdeal.lean#L45-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComponentOfIncIdeal

theorem P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_exists_nat_of_bounds_a5ec014f4cda {x : WithBot ℕ∞} {e : ℕ} (h1 : 1 ≤ x) (h2 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ k : ℕ, x = (k : WithBot ℕ∞) ∧ 1 ≤ k ∧ k ≤ e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComponentOfIncIdeal».«exists_nat_of_bounds» := P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_exists_nat_of_bounds_a5ec014f4cda
