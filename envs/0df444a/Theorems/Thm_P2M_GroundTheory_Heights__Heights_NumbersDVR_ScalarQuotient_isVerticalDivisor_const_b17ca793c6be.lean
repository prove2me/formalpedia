-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_isVerticalDivisor_const_b17ca793c6be
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_isVerticalDivisor_const_b17ca793c6be
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:08:29.014485+00:00
-- url     : https://prove2.me/theorems/7e473bbe-d69a-400f-9f34-f9875e92c73a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient is Vertical Divisor const b17ca793c6be: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient is Vertical Divisor const b17ca7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient is Vertical Divisor const b17ca793c6be construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient is Vertical Divisor const b17ca793c6be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L158-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L158-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [DecidableEq K]
omit [Fintype K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_isVerticalDivisor_const_b17ca793c6be (P : Ideal (MRing ι O)) [P.IsPrime] (ϖ : O) (u : Oˣ) (n : ℕ)
    (hP : (C ((u : O) * ϖ ^ n) : MRing ι O) ∉ P) :
    IsVerticalDivisor P ϖ 0 (C ((u : O) * ϖ ^ n)) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«isVerticalDivisor_const» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_isVerticalDivisor_const_b17ca793c6be
