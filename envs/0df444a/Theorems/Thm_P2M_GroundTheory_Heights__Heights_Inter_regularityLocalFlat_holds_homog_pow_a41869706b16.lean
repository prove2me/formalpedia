-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_pow_a41869706b16
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_pow_a41869706b16
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:15.736324+00:00
-- url     : https://prove2.me/theorems/b70e6166-c7d4-45c1-adde-c178fd252aec
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog pow a41869706b16: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog pow a41869706b16
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog pow a41869706b16 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog pow a41869706b16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean#L67-L73

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_pow_a41869706b16 {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«homog_pow» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_pow_a41869706b16
