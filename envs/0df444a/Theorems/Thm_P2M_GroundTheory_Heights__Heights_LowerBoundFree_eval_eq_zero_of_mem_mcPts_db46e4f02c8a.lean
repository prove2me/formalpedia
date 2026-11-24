-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_eval_eq_zero_of_mem_mcPts_db46e4f02c8a
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_eval_eq_zero_of_mem_mcPts_db46e4f02c8a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:10.961816+00:00
-- url     : https://prove2.me/theorems/814af792-9610-4327-9841-940f7edbce13
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free eval eq zero of mem mc Pts db46e4f02c8a: P2 M Ground Theory Heights  Heights Lower Bound Free eval eq zero of mem mc Pts db46e4f02c8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free eval eq zero of mem mc Pts db46e4f02c8a construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free eval eq zero of mem mc Pts db46e4f02c8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L76-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_eval_eq_zero_of_mem_mcPts_db46e4f02c8a {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    {g : MRing ι} (hg : g ∈ P) : eval z (map (Int.castRingHom ℂ) g) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«eval_eq_zero_of_mem_mcPts» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_eval_eq_zero_of_mem_mcPts_db46e4f02c8a
