-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_eventuallyEq_79f40a77bb7e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_eventuallyEq_79f40a77bb7e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:10.093155+00:00
-- url     : https://prove2.me/theorems/409ba7b9-a535-4c9b-9e43-043cd4ec91f1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step eventually Eq 79f40a77bb7e: P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step eventually Eq 79f40a77bb7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step eventually Eq 79f40a77bb7e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step eventually Eq 79f40a77bb7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTClosure.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTClosure.lean#L22-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTClosure
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
noncomputable section
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_eventuallyEq_79f40a77bb7e (l : List (K → ℤ)) {F G : (K → ℤ) → ℤ}
    (h : F =ᶠ[Filter.atTop] G) :
    l.foldr diffStep F =ᶠ[Filter.atTop] l.foldr diffStep G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«foldr_diffStep_eventuallyEq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_eventuallyEq_79f40a77bb7e
