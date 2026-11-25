-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_one_6db77f3f161a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_one_6db77f3f161a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:49.692973+00:00
-- url     : https://prove2.me/theorems/2572ecbb-9912-4bff-a349-9f8de3128e31
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rat Div one 6db77f3f161a: P2 M Ground Theory Heights  Heights Numbers DVR rat Div one 6db77f3f161a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rat Div one 6db77f3f161a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rat Div one 6db77f3f161a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_one_6db77f3f161a {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) : ratDiv P f 1 = divCycle P f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ratDiv_one» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_one_6db77f3f161a
