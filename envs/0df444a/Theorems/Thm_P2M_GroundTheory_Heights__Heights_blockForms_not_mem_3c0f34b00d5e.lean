-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockForms_not_mem_3c0f34b00d5e
-- name    : P2M_GroundTheory_Heights__Heights_blockForms_not_mem_3c0f34b00d5e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:18.721336+00:00
-- url     : https://prove2.me/theorems/3ae7ddb3-7a8e-4519-9ea4-860b961233fa
-- title:
--   P2 M Ground Theory Heights  Heights block Forms not mem 3c0f34b00d5e: P2 M Ground Theory Heights  Heights block Forms not mem 3c0f34b00d5e
-- statement:
--   The P2 M Ground Theory Heights  Heights block Forms not mem 3c0f34b00d5e construction uses the P2 M Ground Theory Heights  Heights block Forms not mem 3c0f34b00d5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L142-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L142-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_blockForms_not_mem_3c0f34b00d5e (c : (k : ι) → Fin (n k + 1)) (j : Fin ((blockAddData n k₀).size + 1)) :
    (blockAddData n k₀).liftOld (blockForms n k₀ c j) ∉ (blockAddData n k₀).extIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockForms_not_mem» := P2M_GroundTheory_Heights__Heights_blockForms_not_mem_3c0f34b00d5e
