-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_C_pow_mul_mem_62fd3ae53f2d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_C_pow_mul_mem_62fd3ae53f2d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:21.716527+00:00
-- url     : https://prove2.me/theorems/7ffe7ddd-8a40-4c1b-a0ff-78f86da11dad
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem of C pow mul mem 62fd3ae53f2d: P2 M Ground Theory Heights  Heights Numbers DVR mem of C pow mul mem 62fd3ae53f2d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem of C pow mul mem 62fd3ae53f2d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem of C pow mul mem 62fd3ae53f2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGradedPieceFree.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGradedPieceFree.lean#L27-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceFree
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_C_pow_mul_mem_62fd3ae53f2d {O : Type u} [CommRing O] {K : Type} {ι : K → Type}
    {P : Ideal (MRing ι O)} {ϖ : O} (hP : ∀ x, C ϖ * x ∈ P → x ∈ P) :
    ∀ (n : ℕ) (y : MRing ι O), C (ϖ ^ n) * y ∈ P → y ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_of_C_pow_mul_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_C_pow_mul_mem_62fd3ae53f2d
