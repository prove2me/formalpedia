-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_one_block_72430939ba75
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_one_block_72430939ba75
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:43.680499+00:00
-- url     : https://prove2.me/theorems/1070979d-6aaf-5444-88a9-50da01e52eaa
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values one block 72430939ba75: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values one block 724309
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values one block 72430939ba75 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values one block 72430939ba75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L118-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L118-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
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
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_one_block_72430939ba75 {Ω : Type} [Field Ω] (m : ℕ) (x' : Fin (m + 1) → Ω) :
    monomialValues (n := fun _ : Unit ↦ m) (fun p ↦ x' p.2) (fun _ ↦ 1) = Set.range x' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«monomialValues_one_block» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_one_block_72430939ba75
