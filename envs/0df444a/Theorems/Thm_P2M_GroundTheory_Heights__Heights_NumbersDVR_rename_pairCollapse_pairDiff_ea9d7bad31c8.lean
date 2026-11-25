-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_pairDiff_ea9d7bad31c8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_pairDiff_ea9d7bad31c8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:36.058796+00:00
-- url     : https://prove2.me/theorems/dd71b377-594e-4f64-b924-d5e61c6afa23
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rename pair Collapse pair Diff ea9d7bad31c8: P2 M Ground Theory Heights  Heights Numbers DVR rename pair Collapse pair Diff ea9d7bad31c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rename pair Collapse pair Diff ea9d7bad31c8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rename pair Collapse pair Diff ea9d7bad31c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L31-L37

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_pairDiff_ea9d7bad31c8 (p i : Fin n) :
    rename (pairCollapse p) (pairDiff i) = if i = p then 0 else pairDiff i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«rename_pairCollapse_pairDiff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_pairDiff_ea9d7bad31c8
