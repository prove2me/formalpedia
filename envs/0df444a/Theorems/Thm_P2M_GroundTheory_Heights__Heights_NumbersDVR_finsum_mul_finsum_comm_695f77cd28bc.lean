-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_mul_finsum_comm_695f77cd28bc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_mul_finsum_comm_695f77cd28bc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:55.707567+00:00
-- url     : https://prove2.me/theorems/49ffefc0-e0bb-4531-b60e-29d43334fd19
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR finsum mul finsum comm 695f77cd28bc: P2 M Ground Theory Heights  Heights Numbers DVR finsum mul finsum comm 695f77cd28bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR finsum mul finsum comm 695f77cd28bc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR finsum mul finsum comm 695f77cd28bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IdealCycleSupportFinite.lean#L25-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IdealCycleSupportFinite.lean#L25-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IdealCycleSupportFinite
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
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_mul_finsum_comm_695f77cd28bc {α β : Type*} (a : α → ℤ) (c : α → β → ℤ) (n : β → ℤ)
    (ha : (Function.support a).Finite) (hc : ∀ W, (Function.support (c W)).Finite) :
    ∑ᶠ W, a W * ∑ᶠ U, c W U * n U = ∑ᶠ U, (∑ᶠ W, a W * c W U) * n U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«finsum_mul_finsum_comm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_mul_finsum_comm_695f77cd28bc
