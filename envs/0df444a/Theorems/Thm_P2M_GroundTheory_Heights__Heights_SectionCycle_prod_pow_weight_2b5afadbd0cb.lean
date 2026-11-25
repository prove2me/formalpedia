-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_prod_pow_weight_2b5afadbd0cb
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_prod_pow_weight_2b5afadbd0cb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:12.619937+00:00
-- url     : https://prove2.me/theorems/31d09d0d-8074-4af6-bcb1-e41eb3126eba
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle prod pow weight 2b5afadbd0cb: P2 M Ground Theory Heights  Heights Section Cycle prod pow weight 2b5afadbd0cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle prod pow weight 2b5afadbd0cb construction uses the P2 M Ground Theory Heights  Heights Section Cycle prod pow weight 2b5afadbd0cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L125-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L125-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
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
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_prod_pow_weight_2b5afadbd0cb {M : Type*} [CommMonoid M] (t : ι → M) (s : Coord n →₀ ℕ) :
    ∏ k, t k ^ (Finsupp.weight (coordDeg n) s k) = s.prod fun v e ↦ t v.1 ^ e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«prod_pow_weight» := P2M_GroundTheory_Heights__Heights_SectionCycle_prod_pow_weight_2b5afadbd0cb
