-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_block_var_of_weight_pos_b2cd7375c012
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_block_var_of_weight_pos_b2cd7375c012
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:56.720536+00:00
-- url     : https://prove2.me/theorems/10b4b401-7b69-4005-89ad-c0c20f00172f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists block var of weight pos b2cd7375c012: P2 M Ground Theory Heights  Heights Numbers DVR exists block var of weight pos b2cd7375c012
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists block var of weight pos b2cd7375c012 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists block var of weight pos b2cd7375c012 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbFnVanishBlock.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbFnVanishBlock.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbFnVanishBlock
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_block_var_of_weight_pos_b2cd7375c012 {K : Type} [DecidableEq K] {ι : K → Type}
    (d : (Σ k, ι k) →₀ ℕ) (k : K) (h : 1 ≤ Finsupp.weight (blockWeight ι) d k) :
    ∃ v : Σ k, ι k, v.1 = k ∧ d v ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_block_var_of_weight_pos» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_block_var_of_weight_pos_b2cd7375c012
