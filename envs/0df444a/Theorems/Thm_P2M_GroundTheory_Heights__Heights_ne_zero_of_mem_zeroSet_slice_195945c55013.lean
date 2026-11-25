-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ne_zero_of_mem_zeroSet_slice_195945c55013
-- name    : P2M_GroundTheory_Heights__Heights_ne_zero_of_mem_zeroSet_slice_195945c55013
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:46.823689+00:00
-- url     : https://prove2.me/theorems/a0048ea8-a6e4-4357-add4-3cc6b9023013
-- title:
--   P2 M Ground Theory Heights  Heights ne zero of mem zero Set slice 195945c55013: P2 M Ground Theory Heights  Heights ne zero of mem zero Set slice 195945c55013
-- statement:
--   The P2 M Ground Theory Heights  Heights ne zero of mem zero Set slice 195945c55013 construction uses the P2 M Ground Theory Heights  Heights ne zero of mem zero Set slice 195945c55013 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFormIntSymm.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFormIntSymm.lean#L11-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormIntSymm
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_ne_zero_of_mem_zeroSet_slice_195945c55013 {n : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    {x : Fin n → ℂ} (hx : x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) : x ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ne_zero_of_mem_zeroSet_slice» := P2M_GroundTheory_Heights__Heights_ne_zero_of_mem_zeroSet_slice_195945c55013
