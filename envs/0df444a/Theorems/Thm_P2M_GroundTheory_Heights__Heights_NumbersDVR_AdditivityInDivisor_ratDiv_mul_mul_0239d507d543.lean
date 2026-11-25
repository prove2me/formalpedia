-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_mul_mul_0239d507d543
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_mul_mul_0239d507d543
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:05.969404+00:00
-- url     : https://prove2.me/theorems/12403556-0f55-467b-ab99-e2ca563ef5dd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor rat Div mul mul 0239d507d543: P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor rat Div mul mul 0239d507d543
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor rat Div mul mul 0239d507d543 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor rat Div mul mul 0239d507d543 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L58-L64

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_mul_mul_0239d507d543 (hmul : DivCycleMul.Statement.{u}) {O : Type u} [CommRing O] [IsNoetherianRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    {f₁ g₁ f₂ g₂ : MRing ι O} (hf₁ : f₁ ∉ P) (hf₂ : f₂ ∉ P) (hg₁ : g₁ ∉ P) (hg₂ : g₂ ∉ P) :
    ratDiv P (f₁ * f₂) (g₁ * g₂) = ratDiv P f₁ g₁ + ratDiv P f₂ g₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«AdditivityInDivisor».«ratDiv_mul_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_mul_mul_0239d507d543
