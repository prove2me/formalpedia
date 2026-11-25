-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_ker_ce0d18ed1629
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_ker_ce0d18ed1629
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:42.535848+00:00
-- url     : https://prove2.me/theorems/b4574084-9505-4afc-a689-7cd2b1e63f3f
-- title:
--   P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of ker ce0d18ed1629: P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of ker ce0d18ed1629
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of ker ce0d18ed1629 construction uses the P2 M Ground Theory Heights  Heights Inter mixed Disc eq zero of ker ce0d18ed1629 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L90-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L90-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
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
open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_ker_ce0d18ed1629 (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (V : Submodule ℂ (Fin D → ℂ))
    (S : Finset (Fin D)) (hdim : D < Module.finrank ℂ V + S.card) (hA : ∀ k ∈ S, ∀ x ∈ V, A k *ᵥ x = 0) :
    mixedDisc A = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mixedDisc_eq_zero_of_ker» := P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_ker_ce0d18ed1629
