-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_not_lt_lt_of_mem_minimalPrimes_sup_span_d06807dbb20f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_not_lt_lt_of_mem_minimalPrimes_sup_span_d06807dbb20f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:12.570517+00:00
-- url     : https://prove2.me/theorems/2e49cd81-8526-586e-81e8-7d7357ecf811
-- title:
--   P2 M Ground Theory Heights  Heights Vertical not lt lt of mem minimal Primes sup span d06807dbb20f: P2 M Ground Theory Heights  Heights Vertical not lt lt of mem minimal Primes sup span d06807dbb20f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical not lt lt of mem minimal Primes sup span d06807dbb20f construction uses the P2 M Ground Theory Heights  Heights Vertical not lt lt of mem minimal Primes sup span d06807dbb20f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PVertSpec.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PVertSpec.lean#L11-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_not_lt_lt_of_mem_minimalPrimes_sup_span_d06807dbb20f {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [hP : P.IsPrime] [hQ : Q.IsPrime] [hW : W.IsPrime] {x : A}
    (hmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q < W) : False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«not_lt_lt_of_mem_minimalPrimes_sup_span» := P2M_GroundTheory_Heights__Heights_Vertical_not_lt_lt_of_mem_minimalPrimes_sup_span_d06807dbb20f
