-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_0c268acf36e9
-- name    : P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_0c268acf36e9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:16:22.818865+00:00
-- url     : https://prove2.me/theorems/a7b00f39-7195-45ea-8286-d41a89a7b10f
-- title:
--   P2 M Ground Theory Heights  Heights Block Trdeg exists nat mul mem range 0c268acf36e9: P2 M Ground Theory Heights  Heights Block Trdeg exists nat mul mem range 0c268acf36e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Trdeg exists nat mul mem range 0c268acf36e9 construction uses the P2 M Ground Theory Heights  Heights Block Trdeg exists nat mul mem range 0c268acf36e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L21-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
variable {σ : Type} {L : Type} [Field L] [Algebra ℚ L]

theorem P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_0c268acf36e9 (ψ : MvPolynomial σ ℤ →+* L) {y : L}
    (hy : y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : L) * y ∈ ψ.range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockTrdeg».«exists_nat_mul_mem_range» := P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_0c268acf36e9
