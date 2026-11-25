-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_mem_minimalPrimes_of_cross_a4bf0f01ea5d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_mem_minimalPrimes_of_cross_a4bf0f01ea5d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:12.585698+00:00
-- url     : https://prove2.me/theorems/5c9e0c4b-fefa-5564-9cb1-ea9ea4ab2c95
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull mem minimal Primes of cross a4bf0f01ea5d: P2 M Ground Theory Heights  Heights Inter Diag Pull mem minimal Primes of cross a4bf0f01ea5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull mem minimal Primes of cross a4bf0f01ea5d construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull mem minimal Primes of cross a4bf0f01ea5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L21-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_mem_minimalPrimes_of_cross_a4bf0f01ea5d {V W : Ideal R} {f g u v : R} (hrel : f * v - g * u ∈ V)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hu : u ∉ W) (hv : v ∉ W) :
    W ∈ (V ⊔ Ideal.span {g}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«mem_minimalPrimes_of_cross» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_mem_minimalPrimes_of_cross_a4bf0f01ea5d
