-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_zero_nonneg_d7114637c6bd
-- name    : P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_zero_nonneg_d7114637c6bd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:20.413912+00:00
-- url     : https://prove2.me/theorems/d9e3e938-39cb-405b-8886-bfde6a4c14cf
-- title:
--   P2 M Ground Theory Heights  Heights Nef Of Nonneg Alt geo Num zero nonneg d7114637c6bd: P2 M Ground Theory Heights  Heights Nef Of Nonneg Alt geo Num zero nonneg d7114637c6bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Nef Of Nonneg Alt geo Num zero nonneg d7114637c6bd construction uses the P2 M Ground Theory Heights  Heights Nef Of Nonneg Alt geo Num zero nonneg d7114637c6bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PNefOfNonneg.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PNefOfNonneg.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PNefOfNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.NefOfNonnegAlt

theorem P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_zero_nonneg_d7114637c6bd {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NefOfNonnegAlt».«geoNum_zero_nonneg» := P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_zero_nonneg_d7114637c6bd
