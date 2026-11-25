-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointForm_holds_maDensity_eq_zero_2db30437fffd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointForm_holds_maDensity_eq_zero_2db30437fffd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:42.502847+00:00
-- url     : https://prove2.me/theorems/881112f5-9095-5f72-8f0b-ac48243ab271
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form holds ma Density eq zero 2db30437fffd: P2 M Ground Theory Heights  Heights Inter point Form holds ma Density eq zero 2db30437fffd
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form holds ma Density eq zero 2db30437fffd construction uses the P2 M Ground Theory Heights  Heights Inter point Form holds ma Density eq zero 2db30437fffd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MixedDiscEqZeroOfMulVec.lean#L25-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MixedDiscEqZeroOfMulVec.lean#L25-L51

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

theorem P2M_GroundTheory_Heights__Heights_Inter_pointForm_holds_maDensity_eq_zero_2db30437fffd (hR : pointFormRank_holds.Statement) (hE : pointFormEuler_holds.Statement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d n : ℕ}
    {L : Fin n → HermLine ι} {L' : Fin n → HermLine ι'} (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hdn : d < n + 1) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} {y : Fin n → ℂ} {w : ((k : K') → ι' k) → ℂ}
    {γ : (Fin n → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((L' j).h (γ y'))) y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointForm_holds».«maDensity_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_pointForm_holds_maDensity_eq_zero_2db30437fffd
