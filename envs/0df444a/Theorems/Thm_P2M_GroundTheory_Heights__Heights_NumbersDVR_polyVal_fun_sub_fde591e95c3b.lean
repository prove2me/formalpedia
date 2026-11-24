-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_fun_sub_fde591e95c3b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_fun_sub_fde591e95c3b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:07.272792+00:00
-- url     : https://prove2.me/theorems/6b5508b6-a122-4b5c-a81d-be769f59623e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR poly Val fun sub fde591e95c3b: P2 M Ground Theory Heights  Heights Numbers DVR poly Val fun sub fde591e95c3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR poly Val fun sub fde591e95c3b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR poly Val fun sub fde591e95c3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L56-L60

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_fun_sub_fde591e95c3b (A₁ A₂ : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) :
    polyVal (fun l => A₁ l - A₂ l) cls H = polyVal A₁ cls H - polyVal A₂ cls H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«polyVal_fun_sub» := P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_fun_sub_fde591e95c3b
