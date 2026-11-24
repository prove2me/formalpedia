-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_X_mul_dd63c716e8c0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_X_mul_dd63c716e8c0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:17.543915+00:00
-- url     : https://prove2.me/theorems/fa542894-b3ef-482c-8754-304aea032326
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR poly Val X mul dd63c716e8c0: P2 M Ground Theory Heights  Heights Numbers DVR poly Val X mul dd63c716e8c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR poly Val X mul dd63c716e8c0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR poly Val X mul dd63c716e8c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L85-L92

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
variable {K : Type*} {σ τ : Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_X_mul_dd63c716e8c0 {A : List (K → ℤ) → ℤ} (hA : PermInv A) (cls : σ → K → ℤ) (s : σ)
    (H : MvPolynomial σ ℤ) :
    polyVal A cls (X s * H) = polyVal (fun l => A (cls s :: l)) cls H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«polyVal_X_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_X_mul_dd63c716e8c0
