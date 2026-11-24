-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_sub_f8bacce55cb1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_sub_f8bacce55cb1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:46.219455+00:00
-- url     : https://prove2.me/theorems/d44d0e03-4229-49fd-ab0e-096db2426a61
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR poly Val sub f8bacce55cb1: P2 M Ground Theory Heights  Heights Numbers DVR poly Val sub f8bacce55cb1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR poly Val sub f8bacce55cb1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR poly Val sub f8bacce55cb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L46-L48

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_sub_f8bacce55cb1 (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H₁ H₂ : MvPolynomial σ ℤ) :
    polyVal A cls (H₁ - H₂) = polyVal A cls H₁ - polyVal A cls H₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«polyVal_sub» := P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_sub_f8bacce55cb1
