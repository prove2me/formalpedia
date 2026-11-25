-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_smallPowerSum_isHomogeneous_cdf6a1058f11
-- name    : P2M_GroundTheory_Heights__Heights_KRest_smallPowerSum_isHomogeneous_cdf6a1058f11
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:19.78942+00:00
-- url     : https://prove2.me/theorems/6f3fcec2-c164-5477-9e0d-a8fe45f4cade
-- title:
--   P2 M Ground Theory Heights  Heights KRest small Power Sum is Homogeneous cdf6a1058f11: P2 M Ground Theory Heights  Heights KRest small Power Sum is Homogeneous cdf6a1058f11
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest small Power Sum is Homogeneous cdf6a1058f11 construction uses the P2 M Ground Theory Heights  Heights KRest small Power Sum is Homogeneous cdf6a1058f11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCaseSharp.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCaseSharp.lean#L9-L12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCaseSharp
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

theorem P2M_GroundTheory_Heights__Heights_KRest_smallPowerSum_isHomogeneous_cdf6a1058f11 (f r a : ℕ) (cs : RestTerms.SmallBlock) (n : ℕ) (τ : Fin f) :
    (RestTerms.smallPowerSum f r a cs n τ).IsHomogeneous n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«smallPowerSum_isHomogeneous» := P2M_GroundTheory_Heights__Heights_KRest_smallPowerSum_isHomogeneous_cdf6a1058f11
