-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_geoVal_sub_right_babaa13856e5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_geoVal_sub_right_babaa13856e5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:44.063334+00:00
-- url     : https://prove2.me/theorems/fa13f92a-cb93-5c30-80be-49155ac24d9c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR geo Val sub right babaa13856e5: P2 M Ground Theory Heights  Heights Numbers DVR geo Val sub right babaa13856e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR geo Val sub right babaa13856e5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR geo Val sub right babaa13856e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L169-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L169-L183

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_geoVal_sub_right_babaa13856e5 {A : List (K → ℤ) → ℤ} (hp : PermInv A) (ha : HeadAdd A) (k : ℕ)
    (a b c : K → ℤ) :
    geoVal A k a c - geoVal A k a b =
      -polyVal (fun l => A ((b - c) :: l)) ![a, b, c] (geoSum3 k (X 0) (X 1) (X 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«geoVal_sub_right» := P2M_GroundTheory_Heights__Heights_NumbersDVR_geoVal_sub_right_babaa13856e5
