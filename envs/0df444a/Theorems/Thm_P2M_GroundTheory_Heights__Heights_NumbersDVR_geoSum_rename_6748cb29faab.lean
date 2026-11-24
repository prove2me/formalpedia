-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_geoSum_rename_6748cb29faab
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_geoSum_rename_6748cb29faab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:47.73025+00:00
-- url     : https://prove2.me/theorems/79a860da-83da-4b49-a42f-291f559c18da
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR geo Sum rename 6748cb29faab: P2 M Ground Theory Heights  Heights Numbers DVR geo Sum rename 6748cb29faab
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR geo Sum rename 6748cb29faab construction uses the P2 M Ground Theory Heights  Heights Numbers DVR geo Sum rename 6748cb29faab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L155-L157

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
variable {K : Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_geoSum_rename_6748cb29faab {σ τ : Type*} (ρ : σ → τ) (k : ℕ) (s t : σ) :
    rename ρ (geoSum k (X s) (X t) : MvPolynomial σ ℤ) = geoSum k (X (ρ s)) (X (ρ t)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«geoSum_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_geoSum_rename_6748cb29faab
