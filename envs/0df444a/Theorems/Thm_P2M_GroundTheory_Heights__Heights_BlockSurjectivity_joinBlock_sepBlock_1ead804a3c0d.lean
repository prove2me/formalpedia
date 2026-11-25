-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_joinBlock_sepBlock_1ead804a3c0d
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_joinBlock_sepBlock_1ead804a3c0d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:09.940129+00:00
-- url     : https://prove2.me/theorems/b6bc9308-2568-4202-b37b-b092782455ec
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity join Block sep Block 1ead804a3c0d: P2 M Ground Theory Heights  Heights Block Surjectivity join Block sep Block 1ead804a3c0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity join Block sep Block 1ead804a3c0d construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity join Block sep Block 1ead804a3c0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L24-L36

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_joinBlock_sepBlock_1ead804a3c0d (k₀ : ι) (q : MvPolynomial (Coord n) ℤ) :
    joinBlock k₀ (sepBlock k₀ q) = q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«joinBlock_sepBlock» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_joinBlock_sepBlock_1ead804a3c0d
