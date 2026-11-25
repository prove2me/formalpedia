-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_finset_sum_1a44e1bea062
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_finset_sum_1a44e1bea062
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:39.509015+00:00
-- url     : https://prove2.me/theorems/8a4feaa1-51a7-4b86-9ea3-eedb51aa9b3d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Assoc list sum finset sum 1a44e1bea062: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Assoc list sum finset sum 1a44e1bea062
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Assoc list sum finset sum 1a44e1bea062 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Assoc list sum finset sum 1a44e1bea062 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumAssoc.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumAssoc.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumAssoc
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
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_finset_sum_1a44e1bea062 {α β : Type*} (l : List α) (s : Finset β)
    (f : α → β → ℤ) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumAssoc».«list_sum_finset_sum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_finset_sum_1a44e1bea062
