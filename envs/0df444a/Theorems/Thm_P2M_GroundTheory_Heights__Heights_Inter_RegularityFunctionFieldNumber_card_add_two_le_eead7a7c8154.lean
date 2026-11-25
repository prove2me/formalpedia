-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_card_add_two_le_eead7a7c8154
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_card_add_two_le_eead7a7c8154
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:19.872794+00:00
-- url     : https://prove2.me/theorems/fc89740c-10a8-51de-bf1b-229c4d775ea1
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number card add two le eead7a7c8154: P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number card add two le eead
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number card add two le eead7a7c8154 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number card add two le eead7a7c8154 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean#L41-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean#L41-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
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
open GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable [DecidableEq K] {E : Type*} [Field E]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_card_add_two_le_eead7a7c8154 [CharZero E] (ψ : MRing ι →+* E) (j : ∀ k, ι k) (hj : ∀ k, ψ (X ⟨k, j k⟩) = 1)
    {P : Ideal (MRing ι)} [P.IsPrime] (hPh : IsMultiHomogIdeal P)
    (hPψ : ∀ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a → g ∈ P → ψ g = 0)
    {u : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a) (huP : u ∉ P) (hψu : ψ u = 0) :
    ((Fintype.card K + 2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityFunctionFieldNumber».«card_add_two_le» := P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_card_add_two_le_eead7a7c8154
