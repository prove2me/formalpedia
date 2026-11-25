-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_mem_minimalPrimes_6f9a6b133d70
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_mem_minimalPrimes_6f9a6b133d70
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:20:09.210389+00:00
-- url     : https://prove2.me/theorems/b884b2c0-12c7-4265-ac22-25229d44e2eb
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal mem minimal Primes 6f9a6b133d70: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal mem minimal P
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal mem minimal Primes 6f9a6b133d70 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal mem minimal Primes 6f9a6b133d70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L50-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L50-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZ
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
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_mem_minimalPrimes_6f9a6b133d70 {J Q : Ideal (MRing ι)} {n : ℕ} (hQ : IsArithVar Q n) (hJQ : J ≤ Q)
    (hdim : ∀ M ∈ J.minimalPrimes, IsRelevant M → IsHorizontal M → IsArithVar M n) :
    Q ∈ J.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionHorizontal».«mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_mem_minimalPrimes_6f9a6b133d70
