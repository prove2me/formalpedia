-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_block_vars_mem_572dc42ada6f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_block_vars_mem_572dc42ada6f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:36.383339+00:00
-- url     : https://prove2.me/theorems/37653841-8973-4047-bb43-f375d62adf25
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem of block vars mem 572dc42ada6f: P2 M Ground Theory Heights  Heights Numbers DVR mem of block vars mem 572dc42ada6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem of block vars mem 572dc42ada6f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem of block vars mem 572dc42ada6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbFnVanishBlock.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbFnVanishBlock.lean#L23-L39

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_block_vars_mem_572dc42ada6f {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (Q : Ideal (MRing ι F)) (k : K) (hX : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) (m : K → ℕ)
    (hm : 1 ≤ m k) (f : MRing ι F) (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) m) :
    f ∈ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_of_block_vars_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_block_vars_mem_572dc42ada6f
