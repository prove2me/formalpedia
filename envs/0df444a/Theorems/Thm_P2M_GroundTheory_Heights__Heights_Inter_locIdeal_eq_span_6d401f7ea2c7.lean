-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:21.70892+00:00
-- url     : https://prove2.me/theorems/6f1287b1-cd1e-44eb-a65f-42a2023fd7a6
-- title:
--   P2 M Ground Theory Heights  Heights Inter loc Ideal eq span 6d401f7ea2c7: P2 M Ground Theory Heights  Heights Inter loc Ideal eq span 6d401f7ea2c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter loc Ideal eq span 6d401f7ea2c7 construction uses the P2 M Ground Theory Heights  Heights Inter loc Ideal eq span 6d401f7ea2c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocRing.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocRing.lean#L22-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) :
    locIdeal P W y = Ideal.span {(⟨y, hy⟩ : locRing P W)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«locIdeal_eq_span» := P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7
