-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_mul_6491c5235776
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_mul_6491c5235776
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:11:33.860714+00:00
-- url     : https://prove2.me/theorems/96bdd5a1-f7cf-4735-984e-3b68b6dd1f3e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor mul 6491c5235776: P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor mul 6491c5235776
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor mul 6491c5235776 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor mul 6491c5235776 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L419-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L419-L451

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
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
universe u
variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_mul_6491c5235776 {P : Ideal (MRing ι O)} [P.IsPrime] {ϖ : O} {b b' : K → ℤ}
    {f g f' g' : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g)
    (hD' : IsVerticalDivisor P ϖ b' f' g') :
    IsVerticalDivisor P ϖ (b + b') (f * f') (g * g') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isVerticalDivisor_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_mul_6491c5235776
