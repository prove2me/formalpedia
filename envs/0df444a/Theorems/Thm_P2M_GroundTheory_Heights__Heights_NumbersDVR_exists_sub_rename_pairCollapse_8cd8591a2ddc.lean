-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_sub_rename_pairCollapse_8cd8591a2ddc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_sub_rename_pairCollapse_8cd8591a2ddc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:38.53524+00:00
-- url     : https://prove2.me/theorems/132de060-211e-4966-820d-11eb7883217a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists sub rename pair Collapse 8cd8591a2ddc: P2 M Ground Theory Heights  Heights Numbers DVR exists sub rename pair Collapse 8cd8591a2ddc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists sub rename pair Collapse 8cd8591a2ddc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists sub rename pair Collapse 8cd8591a2ddc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L48-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L48-L76

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_sub_rename_pairCollapse_8cd8591a2ddc (p : Fin n) (G : MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    ∃ Q, G - rename (pairCollapse p) G = pairDiff p * Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_sub_rename_pairCollapse» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_sub_rename_pairCollapse_8cd8591a2ddc
