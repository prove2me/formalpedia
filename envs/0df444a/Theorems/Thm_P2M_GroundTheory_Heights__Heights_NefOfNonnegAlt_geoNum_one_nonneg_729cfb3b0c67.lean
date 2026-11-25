-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_one_nonneg_729cfb3b0c67
-- name    : P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_one_nonneg_729cfb3b0c67
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:19.944667+00:00
-- url     : https://prove2.me/theorems/0b3782cb-f15c-45f7-ac12-9eee9dd90661
-- title:
--   P2 M Ground Theory Heights  Heights Nef Of Nonneg Alt geo Num one nonneg 729cfb3b0c67: P2 M Ground Theory Heights  Heights Nef Of Nonneg Alt geo Num one nonneg 729cfb3b0c67
-- statement:
--   The P2 M Ground Theory Heights  Heights Nef Of Nonneg Alt geo Num one nonneg 729cfb3b0c67 construction uses the P2 M Ground Theory Heights  Heights Nef Of Nonneg Alt geo Num one nonneg 729cfb3b0c67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PNefOfNonneg.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PNefOfNonneg.lean#L18-L25

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

theorem P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_one_nonneg_729cfb3b0c67 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 V (fun _ => a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NefOfNonnegAlt».«geoNum_one_nonneg» := P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_one_nonneg_729cfb3b0c67
