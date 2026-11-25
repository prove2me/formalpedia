-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_maximalIdeal_iff_2f60d05acc3b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_maximalIdeal_iff_2f60d05acc3b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:54.230249+00:00
-- url     : https://prove2.me/theorems/40b35290-d14e-4edd-a232-356147d657e3
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem maximal Ideal iff 2f60d05acc3b: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem maximal Ideal iff 2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem maximal Ideal iff 2f60d05acc3b construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem maximal Ideal iff 2f60d05acc3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean#L232-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean#L232-L238

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
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
variable {P W}

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_maximalIdeal_iff_2f60d05acc3b (hPW : P ≤ W) (x : locRing P W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W)
    (hx : (x : FractionRing (MRing ι ⧸ P)) * fracHom P v = fracHom P u) :
    haveI := isLocalRing hPW
    x ∈ maximalIdeal (locRing P W) ↔ u ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«mem_maximalIdeal_iff» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_maximalIdeal_iff_2f60d05acc3b
