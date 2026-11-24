-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_finrank_flag_cd1463bfacd3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_finrank_flag_cd1463bfacd3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:41.031908+00:00
-- url     : https://prove2.me/theorems/be99a367-60d4-4489-a98e-91f0f14ded7d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation finrank flag cd1463bfacd3: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation finrank flag cd1463bfac
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation finrank flag cd1463bfacd3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation finrank flag cd1463bfacd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L20-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairIff
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_finrank_flag_cd1463bfacd3 (w : Module.Basis (Fin N) Ω E) (i : Fin (N + 1)) :
    Module.finrank Ω (Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})) = i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairCharacterisation».«finrank_flag» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_finrank_flag_cd1463bfacd3
