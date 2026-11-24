-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psum_e0d98b62ae64
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psum_e0d98b62ae64
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:53.275174+00:00
-- url     : https://prove2.me/theorems/0d715664-17d8-4019-b958-41b911919997
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous psum e0d98b62ae64: P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous psum e0d98b62ae64
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous psum e0d98b62ae64 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous psum e0d98b62ae64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L216-L219

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psum_e0d98b62ae64 (N k : ℕ) : (psum (Fin N) ℤ k).IsHomogeneous k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isHomogeneous_psum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psum_e0d98b62ae64
