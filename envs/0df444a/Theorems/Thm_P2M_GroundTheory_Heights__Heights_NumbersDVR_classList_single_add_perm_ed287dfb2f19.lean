-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_single_add_perm_ed287dfb2f19
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_single_add_perm_ed287dfb2f19
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:16.533799+00:00
-- url     : https://prove2.me/theorems/07dbe5f7-4f16-520d-8b35-583413169e3f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class List single add perm ed287dfb2f19: P2 M Ground Theory Heights  Heights Numbers DVR class List single add perm ed287dfb2f19
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class List single add perm ed287dfb2f19 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class List single add perm ed287dfb2f19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L232-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L232-L237

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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_single_add_perm_ed287dfb2f19 {σ : Type*} (cls : σ → K → ℤ) (s : σ) (μ : σ →₀ ℕ) :
    (classList cls (Finsupp.single s 1 + μ)).Perm (cls s :: classList cls μ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classList_single_add_perm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_single_add_perm_ed287dfb2f19
