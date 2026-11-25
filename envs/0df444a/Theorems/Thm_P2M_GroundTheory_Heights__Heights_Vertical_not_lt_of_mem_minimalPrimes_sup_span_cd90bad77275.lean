-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_not_lt_of_mem_minimalPrimes_sup_span_cd90bad77275
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_not_lt_of_mem_minimalPrimes_sup_span_cd90bad77275
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:42.245799+00:00
-- url     : https://prove2.me/theorems/f4e77ca2-df2f-48d5-9293-063c39b08dd6
-- title:
--   P2 M Ground Theory Heights  Heights Vertical not lt of mem minimal Primes sup span cd90bad77275: P2 M Ground Theory Heights  Heights Vertical not lt of mem minimal Primes sup span cd90bad77275
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical not lt of mem minimal Primes sup span cd90bad77275 construction uses the P2 M Ground Theory Heights  Heights Vertical not lt of mem minimal Primes sup span cd90bad77275 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFibreCut.lean#L10-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFibreCut.lean#L10-L40

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreCut
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
open MvPolynomial IsDedekindDomain

theorem P2M_GroundTheory_Heights__Heights_Vertical_not_lt_of_mem_minimalPrimes_sup_span_cd90bad77275 {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P W Q : Ideal R} {f : R} [P.IsPrime] [W.IsPrime] (hPW : P < W)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : ¬ W < Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«not_lt_of_mem_minimalPrimes_sup_span» := P2M_GroundTheory_Heights__Heights_Vertical_not_lt_of_mem_minimalPrimes_sup_span_cd90bad77275
