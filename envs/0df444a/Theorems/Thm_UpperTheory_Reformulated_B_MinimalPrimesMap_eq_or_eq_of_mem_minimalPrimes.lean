-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_MinimalPrimesMap_eq_or_eq_of_mem_minimalPrimes
-- name    : UpperTheory.Reformulated.B.MinimalPrimesMap.eq_or_eq_of_mem_minimalPrimes
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:32:32.829942+00:00
-- url     : https://prove2.me/theorems/4c9713f4-5fe6-4bda-a114-ff060a4b3fcf
-- title:
--   Minimal Primes Map: eq or eq of mem minimal Primes
-- statement:
--   The Minimal Primes Map construction uses the eq or eq of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MinimalPrimesMap.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MinimalPrimesMap.lean#L14-L35

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MinimalPrimesMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.MinimalPrimesMap.eq_or_eq_of_mem_minimalPrimes :
    ∀ {A : Type} [inst : CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [hP : P.IsPrime] [hQ : Q.IsPrime] {s : A},
    W ∈ (P ⊔ Ideal.span {s}).minimalPrimes → P ≤ Q → Q ≤ W → Q = P ∨ Q = W := by sorry
