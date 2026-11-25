-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pow_mul_mem_of_le_a4bda775bd33
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pow_mul_mem_of_le_a4bda775bd33
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:00.185802+00:00
-- url     : https://prove2.me/theorems/dcc8abdb-75d0-404c-9101-f2f53b5e5ce0
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover pow mul mem of le a4bda775bd33: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover pow mul mem of le a4bda775bd33
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover pow mul mem of le a4bda775bd33 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover pow mul mem of le a4bda775bd33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L37-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pow_mul_mem_of_le_a4bda775bd33 {f y : Ω} (hf : f ∈ chartRing ℤ x i) {n n' : ℕ}
    (h : f ^ n * y ∈ chartRing ℤ x i) (hn : n ≤ n') : f ^ n' * y ∈ chartRing ℤ x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«pow_mul_mem_of_le» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pow_mul_mem_of_le_a4bda775bd33
