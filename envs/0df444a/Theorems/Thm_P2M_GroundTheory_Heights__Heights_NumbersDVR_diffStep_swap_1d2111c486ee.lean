-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_swap_1d2111c486ee
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_swap_1d2111c486ee
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:10:49.262494+00:00
-- url     : https://prove2.me/theorems/2394cffb-c640-449a-a546-4e52ecef942d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR diff Step swap 1d2111c486ee: P2 M Ground Theory Heights  Heights Numbers DVR diff Step swap 1d2111c486ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR diff Step swap 1d2111c486ee construction uses the P2 M Ground Theory Heights  Heights Numbers DVR diff Step swap 1d2111c486ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L302-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L302-L307

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_swap_1d2111c486ee (b b' : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep b (diffStep b' h) = diffStep b' (diffStep b h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«diffStep_swap» := P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_swap_1d2111c486ee
