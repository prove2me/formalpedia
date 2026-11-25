-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_sameGenericFibre_trans_09b01538ecfc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_sameGenericFibre_trans_09b01538ecfc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:25.964805+00:00
-- url     : https://prove2.me/theorems/6f1032cc-225a-48ae-bec0-9009862772dc
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR same Generic Fibre trans 09b01538ecfc: P2 M Ground Theory Heights  Heights Numbers DVR same Generic Fibre trans 09b01538ecfc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR same Generic Fibre trans 09b01538ecfc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR same Generic Fibre trans 09b01538ecfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L462-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L462-L471

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_sameGenericFibre_trans_09b01538ecfc {τ : Type*} {x : τ → Ω} {ϖ : O} {B B' B'' : ChartBundle O x N E}
    (h₁ : SameGenericFibre ϖ B B') (h₂ : SameGenericFibre ϖ B' B'') : SameGenericFibre ϖ B B'' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«sameGenericFibre_trans» := P2M_GroundTheory_Heights__Heights_NumbersDVR_sameGenericFibre_trans_09b01538ecfc
