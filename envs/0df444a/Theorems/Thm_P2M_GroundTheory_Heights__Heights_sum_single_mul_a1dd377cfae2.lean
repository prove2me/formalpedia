-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_single_mul_a1dd377cfae2
-- name    : P2M_GroundTheory_Heights__Heights_sum_single_mul_a1dd377cfae2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:35.223995+00:00
-- url     : https://prove2.me/theorems/20aee66b-7e4a-4c2d-9f1f-74385acf424c
-- title:
--   P2 M Ground Theory Heights  Heights sum single mul a1dd377cfae2: P2 M Ground Theory Heights  Heights sum single mul a1dd377cfae2
-- statement:
--   The P2 M Ground Theory Heights  Heights sum single mul a1dd377cfae2 construction uses the P2 M Ground Theory Heights  Heights sum single mul a1dd377cfae2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L52-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_sum_single_mul_a1dd377cfae2 {m : ℕ} (σ : K →+* ℂ) (w : Fin m → ℂ) (j : Fin m) (a : K) :
    ∑ j', σ ((Pi.single j a : Fin m → K) j') * w j' = σ a * w j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_single_mul» := P2M_GroundTheory_Heights__Heights_sum_single_mul_a1dd377cfae2
