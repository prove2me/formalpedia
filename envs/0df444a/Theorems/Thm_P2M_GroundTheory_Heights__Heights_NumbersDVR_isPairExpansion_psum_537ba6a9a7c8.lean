-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_psum_537ba6a9a7c8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_psum_537ba6a9a7c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:59.61366+00:00
-- url     : https://prove2.me/theorems/daf6e463-d1c9-4ab3-a430-7d963e1197be
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion psum 537ba6a9a7c8: P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion psum 537ba6a9a7c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion psum 537ba6a9a7c8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion psum 537ba6a9a7c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L170-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L170-L176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_psum_537ba6a9a7c8 (N k : ℕ) :
    IsPairExpansion k (psum (Fin N) ℤ k) (psumExpansion N k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isPairExpansion_psum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_psum_537ba6a9a7c8
