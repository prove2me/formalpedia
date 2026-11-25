-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_pairDiff_7f3a95024044
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_pairDiff_7f3a95024044
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:35.465587+00:00
-- url     : https://prove2.me/theorems/3011902d-8ffe-525f-81bb-eea98c76c9b0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous pair Diff 7f3a95024044: P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous pair Diff 7f3a95024044
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous pair Diff 7f3a95024044 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous pair Diff 7f3a95024044 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L45-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
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
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_pairDiff_7f3a95024044 (i : Fin n) : (pairDiff i).IsHomogeneous 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isHomogeneous_pairDiff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_pairDiff_7f3a95024044
