-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_fn_45f3c9bda240
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_fn_45f3c9bda240
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:41.247496+00:00
-- url     : https://prove2.me/theorems/05dd7743-8c99-4304-a694-3658ff4c86a8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor cyc Eval add fn 45f3c9bda240: P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor cyc Eval add fn 45f3c9bda240
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor cyc Eval add fn 45f3c9bda240 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor cyc Eval add fn 45f3c9bda240 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L22-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtOfAddOneLe
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
open GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_fn_45f3c9bda240 {n n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (h : ∀ W, Z W ≠ 0 → n W = n₁ W + n₂ W) : cycEval n Z = cycEval n₁ Z + cycEval n₂ Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«AdditivityInDivisor».«cycEval_add_fn» := P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_fn_45f3c9bda240
