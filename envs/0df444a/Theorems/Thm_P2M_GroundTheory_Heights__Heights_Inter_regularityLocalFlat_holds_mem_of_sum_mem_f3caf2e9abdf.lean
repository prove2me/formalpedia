-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_sum_mem_f3caf2e9abdf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_sum_mem_f3caf2e9abdf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:29.666491+00:00
-- url     : https://prove2.me/theorems/b042d38b-2956-4239-b842-b5d7188e0ddb
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem of sum mem f3caf2e9abdf: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem of sum mem f3caf2e9abdf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem of sum mem f3caf2e9abdf construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem of sum mem f3caf2e9abdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean#L75-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean#L75-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_sum_mem_f3caf2e9abdf {I : Ideal (MRing ι)} (hI : IsMultiHomogIdeal I) {β : Type*} (s : Finset β)
    (h : β → MRing ι) (d : β → K → ℕ) (hd : Set.InjOn d s) (hh : ∀ b ∈ s, IsMultiHomog (h b) (d b))
    (hsum : ∑ b ∈ s, h b ∈ I) : ∀ b ∈ s, h b ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«mem_of_sum_mem» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_sum_mem_f3caf2e9abdf
