-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_prod_pow_div_dvd_factorial_464682fa385a
-- name    : P2M_GroundTheory_Heights__Heights_Model_prod_pow_div_dvd_factorial_464682fa385a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:11.481626+00:00
-- url     : https://prove2.me/theorems/28181812-9ee1-4fdb-a357-e676a3da291f
-- title:
--   P2 M Ground Theory Heights  Heights Model prod pow div dvd factorial 464682fa385a: P2 M Ground Theory Heights  Heights Model prod pow div dvd factorial 464682fa385a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model prod pow div dvd factorial 464682fa385a construction uses the P2 M Ground Theory Heights  Heights Model prod pow div dvd factorial 464682fa385a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PMertensUpper.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PMertensUpper.lean#L21-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PMertensUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Real

theorem P2M_GroundTheory_Heights__Heights_Model_prod_pow_div_dvd_factorial_464682fa385a (N : ℕ) :
    (∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p)) ∣ N.factorial := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«prod_pow_div_dvd_factorial» := P2M_GroundTheory_Heights__Heights_Model_prod_pow_div_dvd_factorial_464682fa385a
