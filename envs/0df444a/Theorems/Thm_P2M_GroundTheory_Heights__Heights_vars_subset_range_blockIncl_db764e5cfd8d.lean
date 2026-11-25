-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_vars_subset_range_blockIncl_db764e5cfd8d
-- name    : P2M_GroundTheory_Heights__Heights_vars_subset_range_blockIncl_db764e5cfd8d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:51.438676+00:00
-- url     : https://prove2.me/theorems/a859541d-7aa2-40b6-a99d-d8486959b44b
-- title:
--   P2 M Ground Theory Heights  Heights vars subset range block Incl db764e5cfd8d: P2 M Ground Theory Heights  Heights vars subset range block Incl db764e5cfd8d
-- statement:
--   The P2 M Ground Theory Heights  Heights vars subset range block Incl db764e5cfd8d construction uses the P2 M Ground Theory Heights  Heights vars subset range block Incl db764e5cfd8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VarsSubsetRangeBlockIncl.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VarsSubsetRangeBlockIncl.lean#L30-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_vars_subset_range_blockIncl_db764e5cfd8d (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    (f.vars : Set (Coord n)) ⊆ Set.range (blockIncl k₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«vars_subset_range_blockIncl» := P2M_GroundTheory_Heights__Heights_vars_subset_range_blockIncl_db764e5cfd8d
