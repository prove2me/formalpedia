-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psumExpansion_217a129f2629
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psumExpansion_217a129f2629
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:16.501951+00:00
-- url     : https://prove2.me/theorems/9c622f81-d093-474b-92b0-466039419b7b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous psum Expansion 217a129f2629: P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous psum Expansion 217a129f2629
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous psum Expansion 217a129f2629 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous psum Expansion 217a129f2629 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L159-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L159-L168

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psumExpansion_217a129f2629 (N k : ℕ) (i : Fin N) :
    (psumExpansion N k i).IsHomogeneous (k - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isHomogeneous_psumExpansion» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psumExpansion_217a129f2629
