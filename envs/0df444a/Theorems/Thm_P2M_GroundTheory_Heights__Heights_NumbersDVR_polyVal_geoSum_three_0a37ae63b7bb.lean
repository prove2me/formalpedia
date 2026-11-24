-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_geoSum_three_0a37ae63b7bb
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_geoSum_three_0a37ae63b7bb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:25.734302+00:00
-- url     : https://prove2.me/theorems/8e083e9c-3219-4bbc-8fe4-dc3ac051e0e6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR poly Val geo Sum three 0a37ae63b7bb: P2 M Ground Theory Heights  Heights Numbers DVR poly Val geo Sum three 0a37ae63b7bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR poly Val geo Sum three 0a37ae63b7bb construction uses the P2 M Ground Theory Heights  Heights Numbers DVR poly Val geo Sum three 0a37ae63b7bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L159-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L159-L167

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_geoSum_three_0a37ae63b7bb (A : List (K → ℤ) → ℤ) (k : ℕ) (a b c : K → ℤ) (i j : Fin 3) :
    polyVal A ![a, b, c] (geoSum k (X i) (X j)) = geoVal A k (![a, b, c] i) (![a, b, c] j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«polyVal_geoSum_three» := P2M_GroundTheory_Heights__Heights_NumbersDVR_polyVal_geoSum_three_0a37ae63b7bb
