-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_isWeightedHomogeneous_sepBlock_9e2d0892eba8
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_isWeightedHomogeneous_sepBlock_9e2d0892eba8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:54.954547+00:00
-- url     : https://prove2.me/theorems/31a9ad9d-21ac-4486-9517-b28d85fd7ec0
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity is Weighted Homogeneous sep Block 9e2d0892eba8: P2 M Ground Theory Heights  Heights Block Surjectivity is Weighted Homogeneous sep Block 9e2d0892
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity is Weighted Homogeneous sep Block 9e2d0892eba8 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity is Weighted Homogeneous sep Block 9e2d0892eba8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L92-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L92-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_isWeightedHomogeneous_sepBlock_9e2d0892eba8 (k₀ : ι) {q : MvPolynomial (Coord n) ℤ} {m : ι → ℕ}
    (hq : IsWeightedHomogeneous (coordDeg n) q m) :
    IsWeightedHomogeneous (coordDeg n) (sepBlock k₀ q) (Function.update m k₀ 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«isWeightedHomogeneous_sepBlock» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_isWeightedHomogeneous_sepBlock_9e2d0892eba8
