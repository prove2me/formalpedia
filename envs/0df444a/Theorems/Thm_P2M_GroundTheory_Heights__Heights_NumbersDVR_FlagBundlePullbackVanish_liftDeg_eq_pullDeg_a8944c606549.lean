-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_liftDeg_eq_pullDeg_a8944c606549
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_liftDeg_eq_pullDeg_a8944c606549
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:52.437965+00:00
-- url     : https://prove2.me/theorems/447f8ef5-f966-53a2-8fa9-24a3e94a65e8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Pullback Vanish lift Deg eq pull Deg a8944c606549: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Pullback Vanish lift Deg eq p
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Pullback Vanish lift Deg eq pull Deg a8944c606549 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Pullback Vanish lift Deg eq pull Deg a8944c606549 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundlePullbackVanish.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundlePullbackVanish.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundlePullbackVanish
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_liftDeg_eq_pullDeg_a8944c606549 {K : Type*} (L : K → ℤ) :
    liftDeg L = FieldNumbers.pullDeg Function.Embedding.some L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundlePullbackVanish».«liftDeg_eq_pullDeg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_liftDeg_eq_pullDeg_a8944c606549
