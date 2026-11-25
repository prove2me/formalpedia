-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockImage_mConeMap_rename_12896742ddc3
-- name    : P2M_GroundTheory_Heights__Heights_BlockImage_mConeMap_rename_12896742ddc3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:54:37.921435+00:00
-- url     : https://prove2.me/theorems/0428fc5a-f4df-4556-8046-720b3b1727fd
-- title:
--   P2 M Ground Theory Heights  Heights Block Image m Cone Map rename 12896742ddc3: P2 M Ground Theory Heights  Heights Block Image m Cone Map rename 12896742ddc3
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Image m Cone Map rename 12896742ddc3 construction uses the P2 M Ground Theory Heights  Heights Block Image m Cone Map rename 12896742ddc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean#L63-L73

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

theorem P2M_GroundTheory_Heights__Heights_BlockImage_mConeMap_rename_12896742ddc3 (y : Coord n → Ω) (k₀ : ι)
    (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    Geo.mConeMap (ι := blockIdx n) y (rename (blockIncl k₀) f) =
      rename (fun _ : Unit ↦ k₀)
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockImage».«mConeMap_rename» := P2M_GroundTheory_Heights__Heights_BlockImage_mConeMap_rename_12896742ddc3
