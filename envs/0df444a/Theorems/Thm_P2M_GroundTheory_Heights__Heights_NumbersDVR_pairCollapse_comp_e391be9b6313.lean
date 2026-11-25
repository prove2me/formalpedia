-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairCollapse_comp_e391be9b6313
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pairCollapse_comp_e391be9b6313
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:27.306523+00:00
-- url     : https://prove2.me/theorems/76cc50ef-22cf-53fe-9478-b03e1c96aa3e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR pair Collapse comp e391be9b6313: P2 M Ground Theory Heights  Heights Numbers DVR pair Collapse comp e391be9b6313
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR pair Collapse comp e391be9b6313 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR pair Collapse comp e391be9b6313 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L22-L25

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pairCollapse_comp_e391be9b6313 (p : Fin n) : pairCollapse p ∘ pairCollapse p = pairCollapse p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pairCollapse_comp» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pairCollapse_comp_e391be9b6313
