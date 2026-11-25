-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_coordPow_1bf5c2991c29
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_coordPow_1bf5c2991c29
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:44:44.077053+00:00
-- url     : https://prove2.me/theorems/6f20e6fa-cd53-42ff-b882-2e4190ba31d6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Ring is Multi Homog coord Pow 1bf5c2991c29: P2 M Ground Theory Heights  Heights Inter Semiloc Ring is Multi Homog coord Pow 1bf5c2991c29
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Ring is Multi Homog coord Pow 1bf5c2991c29 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Ring is Multi Homog coord Pow 1bf5c2991c29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean#L162-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean#L162-L176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_coordPow_1bf5c2991c29 (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRing».«isMultiHomog_coordPow» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_coordPow_1bf5c2991c29
