-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_idem_785cf95a1311
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_idem_785cf95a1311
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:22.359116+00:00
-- url     : https://prove2.me/theorems/2ed3e9ee-81bf-5bfd-8c43-51953318413e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rename pair Collapse idem 785cf95a1311: P2 M Ground Theory Heights  Heights Numbers DVR rename pair Collapse idem 785cf95a1311
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rename pair Collapse idem 785cf95a1311 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rename pair Collapse idem 785cf95a1311 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L27-L29

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_idem_785cf95a1311 (p : Fin n) (G : MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    rename (pairCollapse p) (rename (pairCollapse p) G) = rename (pairCollapse p) G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«rename_pairCollapse_idem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_idem_785cf95a1311
