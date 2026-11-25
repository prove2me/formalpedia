-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockImage_birational_of_block_ab8106bdde24
-- name    : P2M_GroundTheory_Heights__Heights_BlockImage_birational_of_block_ab8106bdde24
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:12.815583+00:00
-- url     : https://prove2.me/theorems/745be7d9-8924-40f8-99f8-751bb1d064db
-- title:
--   P2 M Ground Theory Heights  Heights Block Image birational of block ab8106bdde24: P2 M Ground Theory Heights  Heights Block Image birational of block ab8106bdde24
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Image birational of block ab8106bdde24 construction uses the P2 M Ground Theory Heights  Heights Block Image birational of block ab8106bdde24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean#L97-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean#L97-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_BirationalOfBlock
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.BlockImage
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {Ω : Type} [Field Ω]
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_BlockImage_birational_of_block_ab8106bdde24 (y : Coord n → Ω) (k₀ : ι)
    (hB : Geo.Birational (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) :
    Geo.Birational (ι := blockIdx n) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockImage».«birational_of_block» := P2M_GroundTheory_Heights__Heights_BlockImage_birational_of_block_ab8106bdde24
