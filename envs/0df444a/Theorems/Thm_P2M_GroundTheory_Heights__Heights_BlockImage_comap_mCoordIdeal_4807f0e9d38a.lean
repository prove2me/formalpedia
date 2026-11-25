-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockImage_comap_mCoordIdeal_4807f0e9d38a
-- name    : P2M_GroundTheory_Heights__Heights_BlockImage_comap_mCoordIdeal_4807f0e9d38a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:54:01.773781+00:00
-- url     : https://prove2.me/theorems/1cfefdf3-1268-5821-a0d0-4acdb8dd6274
-- title:
--   P2 M Ground Theory Heights  Heights Block Image comap m Coord Ideal 4807f0e9d38a: P2 M Ground Theory Heights  Heights Block Image comap m Coord Ideal 4807f0e9d38a
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Image comap m Coord Ideal 4807f0e9d38a construction uses the P2 M Ground Theory Heights  Heights Block Image comap m Coord Ideal 4807f0e9d38a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean#L77-L83

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_BlockImage_comap_mCoordIdeal_4807f0e9d38a (y : Coord n → Ω) (k₀ : ι) :
    (Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀)) =
      Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockImage».«comap_mCoordIdeal» := P2M_GroundTheory_Heights__Heights_BlockImage_comap_mCoordIdeal_4807f0e9d38a
