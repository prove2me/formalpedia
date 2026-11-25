-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_le_weight_block_a95d776f8a10
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_le_weight_block_a95d776f8a10
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:47.12415+00:00
-- url     : https://prove2.me/theorems/81ae512d-06c2-427d-9961-75d1894ab616
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero le weight block a95d776f8a10: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero le weight block a95d776f8a10
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero le weight block a95d776f8a10 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero le weight block a95d776f8a10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalEqOfVdeg.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalEqOfVdeg.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalEqOfVdeg
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
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_le_weight_block_a95d776f8a10 {κ : Type} [DecidableEq κ] {τ : κ → Type} (c : (Σ o, τ o) →₀ ℕ) {p : Σ o, τ o}
    (hp : p ∈ c.support) : c p ≤ Finsupp.weight (blockWeight τ) c p.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagDegreeZero».«le_weight_block» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_le_weight_block_a95d776f8a10
