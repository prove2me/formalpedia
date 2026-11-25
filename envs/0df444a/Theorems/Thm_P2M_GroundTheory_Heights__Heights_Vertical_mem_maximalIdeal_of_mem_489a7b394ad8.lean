-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_mem_maximalIdeal_of_mem_489a7b394ad8
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_mem_maximalIdeal_of_mem_489a7b394ad8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:47.647857+00:00
-- url     : https://prove2.me/theorems/9ab5e45a-a67e-5b1e-b595-492789dab2c8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical mem maximal Ideal of mem 489a7b394ad8: P2 M Ground Theory Heights  Heights Vertical mem maximal Ideal of mem 489a7b394ad8
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical mem maximal Ideal of mem 489a7b394ad8 construction uses the P2 M Ground Theory Heights  Heights Vertical mem maximal Ideal of mem 489a7b394ad8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecMax.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecMax.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_mem_maximalIdeal_of_mem_489a7b394ad8 (e : ℕ) (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ∈ v.asIdeal) :
    algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a) ∈
      IsLocalRing.maximalIdeal (ParDVR e n v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«mem_maximalIdeal_of_mem» := P2M_GroundTheory_Heights__Heights_Vertical_mem_maximalIdeal_of_mem_489a7b394ad8
