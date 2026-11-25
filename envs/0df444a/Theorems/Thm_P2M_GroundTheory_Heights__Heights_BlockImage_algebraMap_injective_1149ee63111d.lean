-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockImage_algebraMap_injective_1149ee63111d
-- name    : P2M_GroundTheory_Heights__Heights_BlockImage_algebraMap_injective_1149ee63111d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:54:03.80653+00:00
-- url     : https://prove2.me/theorems/5e478fe2-08e4-55e0-a6ca-3c3841450640
-- title:
--   P2 M Ground Theory Heights  Heights Block Image algebra Map injective 1149ee63111d: P2 M Ground Theory Heights  Heights Block Image algebra Map injective 1149ee63111d
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Image algebra Map injective 1149ee63111d construction uses the P2 M Ground Theory Heights  Heights Block Image algebra Map injective 1149ee63111d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean#L85-L93

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

theorem P2M_GroundTheory_Heights__Heights_BlockImage_algebraMap_injective_1149ee63111d {K : Type} {κ : K → Type} (I : Ideal (Geo.MRing κ))
    (h : Geo.IsHorizontal I) : Function.Injective (algebraMap ℤ (Geo.MRing κ ⧸ I)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockImage».«algebraMap_injective» := P2M_GroundTheory_Heights__Heights_BlockImage_algebraMap_injective_1149ee63111d
