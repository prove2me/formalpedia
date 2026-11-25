-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_finset_287ad278de3d
-- name    : P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_finset_287ad278de3d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:58.689678+00:00
-- url     : https://prove2.me/theorems/fc31bf0e-7dcc-468b-bb1d-eff5b76dd271
-- title:
--   P2 M Ground Theory Heights  Heights Block Trdeg exists nat mul mem range finset 287ad278de3d: P2 M Ground Theory Heights  Heights Block Trdeg exists nat mul mem range finset 287ad278de3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Trdeg exists nat mul mem range finset 287ad278de3d construction uses the P2 M Ground Theory Heights  Heights Block Trdeg exists nat mul mem range finset 287ad278de3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L46-L59

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

theorem P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_finset_287ad278de3d (ψ : MvPolynomial σ ℤ →+* L) (s : Finset L)
    (hs : ∀ y ∈ s, y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ y ∈ s, (n : L) * y ∈ ψ.range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockTrdeg».«exists_nat_mul_mem_range_finset» := P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_finset_287ad278de3d
