-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_perm_12a838203ed6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_perm_12a838203ed6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:13.027301+00:00
-- url     : https://prove2.me/theorems/6bc8a134-0cc5-56b2-97f7-76ea71f94187
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step perm 12a838203ed6: P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step perm 12a838203ed6
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step perm 12a838203ed6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step perm 12a838203ed6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L216-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L216-L224

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_perm_12a838203ed6 {l₁ l₂ : List (K → ℤ)} (hl : l₁.Perm l₂) (h : (K → ℤ) → ℤ) :
    l₁.foldr diffStep h = l₂.foldr diffStep h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«foldr_diffStep_perm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_perm_12a838203ed6
