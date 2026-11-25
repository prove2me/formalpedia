-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_mulVec_eec48391f62a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_mulVec_eec48391f62a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:14.493209+00:00
-- url     : https://prove2.me/theorems/93f367c3-47d7-49e3-a8a6-ed7f300f96db
-- title:
--   P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of mul Vec eec48391f62a: P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of mul Vec eec48391f62a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of mul Vec eec48391f62a construction uses the P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of mul Vec eec48391f62a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MixedDiscEqZeroOfMulVec.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MixedDiscEqZeroOfMulVec.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MixedDiscEqZeroOfMulVec
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_mulVec_eec48391f62a {D : ℕ} {A : Fin D → Matrix (Fin D) (Fin D) ℂ} {u : Fin D → ℂ} (hu : u ≠ 0)
    (hA : ∀ k, A k *ᵥ u = 0) : mixedDisc A = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mixedDisc_eq_zero_of_mulVec» := P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_mulVec_eec48391f62a
