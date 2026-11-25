-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_eq_polyVal_bf23e9c95722
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_eq_polyVal_bf23e9c95722
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:48.760835+00:00
-- url     : https://prove2.me/theorems/937ef740-3273-4a91-9ba8-2cbaaa423ed2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class Num eq poly Val bf23e9c95722: P2 M Ground Theory Heights  Heights Numbers DVR class Num eq poly Val bf23e9c95722
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class Num eq poly Val bf23e9c95722 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class Num eq poly Val bf23e9c95722 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L539-L550
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L539-L550

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_eq_polyVal_bf23e9c95722 {σ : Type*} (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ}
    (hH : H.IsHomogeneous n) {Q : List (K → ℤ)} {d : ℕ} (hn : n + Q.length = d)
    (W : Ideal (MRing ι O)) : classNum cls H Q W = polyVal (listNum W Q d) cls H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classNum_eq_polyVal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_eq_polyVal_bf23e9c95722
