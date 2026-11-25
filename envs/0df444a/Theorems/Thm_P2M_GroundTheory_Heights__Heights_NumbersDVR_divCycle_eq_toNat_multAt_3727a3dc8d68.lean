-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_toNat_multAt_3727a3dc8d68
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_toNat_multAt_3727a3dc8d68
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:46.111539+00:00
-- url     : https://prove2.me/theorems/0bc29e40-a366-4db3-8b63-e11911652ab4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq to Nat mult At 3727a3dc8d68: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq to Nat mult At 3727a3dc8d68
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq to Nat mult At 3727a3dc8d68 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq to Nat mult At 3727a3dc8d68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L168-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L168-L180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_toNat_multAt_3727a3dc8d68 {P : Ideal (MRing ι R)} (f g : MRing ι R)
    {W : Ideal (MRing ι R)} [W.IsPrime] (hW : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes)
    (hrel : IsRelevant W) (hle : P ⊔ Ideal.span {g} ≤ P ⊔ Ideal.span {f}) :
    divCycle P f W = ((multAt (P ⊔ Ideal.span {f}) W).toNat : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_eq_toNat_multAt» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_toNat_multAt_3727a3dc8d68
