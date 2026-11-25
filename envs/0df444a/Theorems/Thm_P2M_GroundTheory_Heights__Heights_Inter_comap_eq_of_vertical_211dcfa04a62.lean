-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_comap_eq_of_vertical_211dcfa04a62
-- name    : P2M_GroundTheory_Heights__Heights_Inter_comap_eq_of_vertical_211dcfa04a62
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:41.197209+00:00
-- url     : https://prove2.me/theorems/05b8b2c6-c37b-43c5-b658-1bf58eb15beb
-- title:
--   P2 M Ground Theory Heights  Heights Inter comap eq of vertical 211dcfa04a62: P2 M Ground Theory Heights  Heights Inter comap eq of vertical 211dcfa04a62
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter comap eq of vertical 211dcfa04a62 construction uses the P2 M Ground Theory Heights  Heights Inter comap eq of vertical 211dcfa04a62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L169-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_comap_eq_of_vertical_211dcfa04a62 {W U : Ideal (MRing ι)} [W.IsPrime] [U.IsPrime] (hv : ¬ IsHorizontal W)
    (hWU : W ≤ U) : U.comap (C : ℤ →+* MRing ι) = W.comap (C : ℤ →+* MRing ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«comap_eq_of_vertical» := P2M_GroundTheory_Heights__Heights_Inter_comap_eq_of_vertical_211dcfa04a62
