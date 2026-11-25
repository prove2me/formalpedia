-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_of_perm_19c0e0c00719
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_of_perm_19c0e0c00719
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:01.903858+00:00
-- url     : https://prove2.me/theorems/de69cca5-1e1d-4ffa-aa6b-d3ba8c2fa704
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR v Num L eq of perm 19c0e0c00719: P2 M Ground Theory Heights  Heights Numbers DVR v Num L eq of perm 19c0e0c00719
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR v Num L eq of perm 19c0e0c00719 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR v Num L eq of perm 19c0e0c00719 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L311-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L311-L316

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_of_perm_19c0e0c00719 (W : Ideal (MRing ι O)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    vNumL W l = vNumL W l' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«vNumL_eq_of_perm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_of_perm_19c0e0c00719
