-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_not_lt_lt_of_mem_minimalPrimes__7de09ae16e16
-- name    : P2M_GroundTheory_Heights__Heights_Inter_not_lt_lt_of_mem_minimalPrimes__7de09ae16e16
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:05.885203+00:00
-- url     : https://prove2.me/theorems/93f95655-0ceb-4cfc-ad04-c9ffe69dad5a
-- title:
--   P2 M Ground Theory Heights  Heights Inter not lt lt of mem minimal Primes  7de09ae16e16: P2 M Ground Theory Heights  Heights Inter not lt lt of mem minimal Primes  7de09ae16e16
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter not lt lt of mem minimal Primes  7de09ae16e16 construction uses the P2 M Ground Theory Heights  Heights Inter not lt lt of mem minimal Primes  7de09ae16e16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L60-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L60-L91

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
variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_not_lt_lt_of_mem_minimalPrimes__7de09ae16e16 {V W W' : Ideal R} [V.IsPrime] [W'.IsPrime] {x : R}
    (hW : W ∈ (V ⊔ Ideal.span {x}).minimalPrimes) (hVW' : V < W') (hW'W : W' < W) : False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«not_lt_lt_of_mem_minimalPrimes'» := P2M_GroundTheory_Heights__Heights_Inter_not_lt_lt_of_mem_minimalPrimes__7de09ae16e16
