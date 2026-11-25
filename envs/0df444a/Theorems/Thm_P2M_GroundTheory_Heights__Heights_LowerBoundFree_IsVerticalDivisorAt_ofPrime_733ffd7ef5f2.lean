-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_IsVerticalDivisorAt_ofPrime_733ffd7ef5f2
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_IsVerticalDivisorAt_ofPrime_733ffd7ef5f2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:41.268104+00:00
-- url     : https://prove2.me/theorems/aff59d32-f76d-424e-bb8a-1fa39483b244
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Is Vertical Divisor At of Prime 733ffd7ef5f2: P2 M Ground Theory Heights  Heights Lower Bound Free Is Vertical Divisor At of Prime 733ffd7ef5f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Is Vertical Divisor At of Prime 733ffd7ef5f2 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Is Vertical Divisor At of Prime 733ffd7ef5f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals.lean#L141-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals.lean#L141-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_IsVerticalDivisorAt_ofPrime_733ffd7ef5f2 {P : Ideal (MRing ι)} (hP : IsHorizontal P) {p : ℕ}
    (hp : p ≠ 0) : IsVerticalDivisorAt P p 0 (C (p : ℤ)) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«IsVerticalDivisorAt».«ofPrime» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_IsVerticalDivisorAt_ofPrime_733ffd7ef5f2
