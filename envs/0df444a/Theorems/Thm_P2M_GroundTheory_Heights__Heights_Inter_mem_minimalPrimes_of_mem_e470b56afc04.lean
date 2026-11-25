-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_minimalPrimes_of_mem_e470b56afc04
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mem_minimalPrimes_of_mem_e470b56afc04
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:34:44.572011+00:00
-- url     : https://prove2.me/theorems/3a19c741-1818-5110-a41f-9c9d646892a0
-- title:
--   P2 M Ground Theory Heights  Heights Inter mem minimal Primes of mem e470b56afc04: P2 M Ground Theory Heights  Heights Inter mem minimal Primes of mem e470b56afc04
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mem minimal Primes of mem e470b56afc04 construction uses the P2 M Ground Theory Heights  Heights Inter mem minimal Primes of mem e470b56afc04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L93-L104

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

theorem P2M_GroundTheory_Heights__Heights_Inter_mem_minimalPrimes_of_mem_e470b56afc04 {P W : Ideal R} [P.IsPrime] {s t : R}
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) (htP : t ∉ P) (htW : t ∈ W) :
    W ∈ (P ⊔ Ideal.span {t}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mem_minimalPrimes_of_mem» := P2M_GroundTheory_Heights__Heights_Inter_mem_minimalPrimes_of_mem_e470b56afc04
