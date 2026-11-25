-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_mcPts_span_singleton_3b58c335091c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mem_mcPts_span_singleton_3b58c335091c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:58.42363+00:00
-- url     : https://prove2.me/theorems/8db21b52-0e0b-41ff-a8b2-4b08a9fab7d2
-- title:
--   P2 M Ground Theory Heights  Heights Inter mem mc Pts span singleton 3b58c335091c: P2 M Ground Theory Heights  Heights Inter mem mc Pts span singleton 3b58c335091c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mem mc Pts span singleton 3b58c335091c construction uses the P2 M Ground Theory Heights  Heights Inter mem mc Pts span singleton 3b58c335091c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PZeroSetNull.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PZeroSetNull.lean#L10-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PZeroSetNull
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_mem_mcPts_span_singleton_3b58c335091c {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hs : eval z (map (Int.castRingHom ℂ) s) = 0) : z ∈ mcPts (Ideal.span {s}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mem_mcPts_span_singleton» := P2M_GroundTheory_Heights__Heights_Inter_mem_mcPts_span_singleton_3b58c335091c
