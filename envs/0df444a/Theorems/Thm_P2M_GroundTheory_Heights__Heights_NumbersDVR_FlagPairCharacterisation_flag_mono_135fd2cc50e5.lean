-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_mono_135fd2cc50e5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_mono_135fd2cc50e5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:55.665177+00:00
-- url     : https://prove2.me/theorems/454eff21-1ab1-5fe1-ae0e-52fb012d9698
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation flag mono 135fd2cc50e5: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation flag mono 135fd2cc50e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation flag mono 135fd2cc50e5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation flag mono 135fd2cc50e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L40-L42

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_mono_135fd2cc50e5 (w : Module.Basis (Fin N) Ω E) :
    Monotone fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairCharacterisation».«flag_mono» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_mono_135fd2cc50e5
