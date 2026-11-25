-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_contract_intersection_number_28dd973e576a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_contract_intersection_number_28dd973e576a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:52.740502+00:00
-- url     : https://prove2.me/theorems/2fe3612d-b534-56e7-8c9b-2bf64b8e659a
-- title:
--   P2 M Ground Theory Heights  Heights Inter contract intersection number 28dd973e576a: P2 M Ground Theory Heights  Heights Inter contract intersection number 28dd973e576a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter contract intersection number 28dd973e576a construction uses the P2 M Ground Theory Heights  Heights Inter contract intersection number 28dd973e576a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L111-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L111-L208

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Inter_contract_intersection_number_28dd973e576a (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement)
    (I : AllFam) (hI : I.IsFamily) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (P' : Ideal (MRing ι')) (d : ℕ) (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι'),
      IsArithVar P' n → IsArithVar (imageZ v P') d → d < n → (∀ j, IsSmoothHerm (L j)) →
      (∀ j, IsPullHerm κ v (L j) (L' j)) → I K' ι' P' n L' = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«contract_intersection_number» := P2M_GroundTheory_Heights__Heights_Inter_contract_intersection_number_28dd973e576a
